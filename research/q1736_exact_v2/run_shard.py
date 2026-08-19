#!/usr/bin/env python3
"""Run one resumable shard of the complete fixed-P [[17,3,6]] search."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
import traceback
from pathlib import Path

from q1736_core import (
    D,
    columns_from_counts,
    enumerate_p_types,
    generate_fixed_p_xcnf,
    parse_cms_model,
    verify_graph_candidate,
)


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def cms_smoke_test(cms: Path, work: Path) -> dict[str, object]:
    """Check native XOR syntax and model output before generating large cases."""
    smoke = work / "cms_xor_smoke.cnf"
    # x-1 2 0 means (not x1) XOR x2 = 1, equivalently x1=x2.
    smoke.write_text("p cnf 2 2\nx-1 2 0\n1 0\n")
    completed = subprocess.run(
        [str(cms), "--verb=0", "--printsol=1", str(smoke)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=60,
        check=False,
    )
    output = completed.stdout
    if completed.returncode != 10 or "SATISFIABLE" not in output:
        raise RuntimeError(
            f"CryptoMiniSat XOR smoke test failed with exit {completed.returncode}:\n{output}"
        )
    assignment = parse_cms_model(output)
    if assignment.get(1) is not True or assignment.get(2) is not True:
        raise RuntimeError(f"unexpected smoke-test model: {assignment}")
    return {
        "returncode": completed.returncode,
        "model": {str(key): value for key, value in sorted(assignment.items())},
        "output_tail": output[-2000:],
    }


def normalize_xor_prefix(path: Path) -> None:
    """Convert the generator's readable `x -1 ...` lines to CMS `x-1 ...`."""
    replacement = path.with_suffix(path.suffix + ".normalized")
    with path.open("rb", buffering=1024 * 1024) as source, replacement.open(
        "wb", buffering=1024 * 1024
    ) as target:
        for line in source:
            if line.startswith(b"x "):
                target.write(b"x" + line[2:])
            else:
                target.write(line)
    replacement.replace(path)


def classify_solver_output(returncode: int, output: str, timed_out: bool) -> str:
    if timed_out:
        return "TIMEOUT"
    if returncode == 10 and "SATISFIABLE" in output and "UNSATISFIABLE" not in output:
        return "SAT"
    if returncode == 20 and "UNSATISFIABLE" in output:
        return "UNSAT"
    return "UNKNOWN"


def run_solver(cms: Path, instance: Path, timeout_seconds: int) -> dict[str, object]:
    command = [str(cms), "--verb=0", "--printsol=1", str(instance)]
    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
        returncode = completed.returncode
        output = completed.stdout
    except subprocess.TimeoutExpired as error:
        timed_out = True
        returncode = 124
        stdout = error.stdout or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        output = stdout
    elapsed = time.monotonic() - started
    return {
        "command": command,
        "returncode": returncode,
        "timed_out": timed_out,
        "elapsed_seconds": elapsed,
        "status": classify_solver_output(returncode, output, timed_out),
        "output": output,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cms", type=Path, required=True)
    parser.add_argument("--shard", type=int, required=True)
    parser.add_argument("--shards", type=int, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--max-types", type=int, default=0)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    args = parser.parse_args()

    if not 0 <= args.shard < args.shards:
        parser.error("shard must lie in [0,shards)")
    if not args.cms.is_file():
        parser.error(f"CryptoMiniSat binary not found: {args.cms}")
    args.work.mkdir(parents=True, exist_ok=True)
    args.results.mkdir(parents=True, exist_ok=True)

    smoke = cms_smoke_test(args.cms, args.work)
    all_types = enumerate_p_types()
    eligible = [entry for entry in all_types if entry["minimum_logical_weight"] >= D]
    # Hard-looking balanced logical types are attempted early, while the stable
    # type_id remains the certificate identifier.
    eligible.sort(
        key=lambda entry: (
            -int(entry["minimum_logical_weight"]),
            int(entry["maximum_logical_weight"]) - int(entry["minimum_logical_weight"]),
            int(entry["counts"][0]),
            int(entry["type_id"]),
        )
    )
    assigned = [entry for position, entry in enumerate(eligible) if position % args.shards == args.shard]
    if args.max_types > 0:
        assigned = assigned[: args.max_types]

    summary_path = args.results / f"shard_{args.shard:02d}.json"
    summary: dict[str, object] = {
        "format": "q1736-fixed-P-campaign-v2",
        "shard": args.shard,
        "shards": args.shards,
        "timeout_seconds_per_type": args.timeout,
        "all_p_types": len(all_types),
        "eligible_p_types": len(eligible),
        "assigned_type_ids": [entry["type_id"] for entry in assigned],
        "smoke_test": smoke,
        "results": [],
        "sat_candidate": None,
        "complete": False,
    }
    atomic_json(summary_path, summary)

    for position, entry in enumerate(assigned):
        type_id = int(entry["type_id"])
        prefix = f"type_{type_id:03d}"
        instance = args.work / f"{prefix}.cnf"
        metadata_path = args.results / f"{prefix}_instance.json"
        solver_log = args.results / f"{prefix}_solver.log"
        record: dict[str, object] = {
            "type": entry,
            "position_in_shard": position,
            "status": "STARTED",
        }
        summary["current_type_id"] = type_id
        atomic_json(summary_path, summary)

        try:
            columns = columns_from_counts(entry["counts"])
            generation_started = time.monotonic()
            metadata = generate_fixed_p_xcnf(columns, instance, metadata_path)
            normalize_xor_prefix(instance)
            generation_seconds = time.monotonic() - generation_started
            solver = run_solver(args.cms, instance, args.timeout)
            output = str(solver.pop("output"))
            solver_log.write_text(output)
            record.update(
                {
                    "status": solver["status"],
                    "generation_seconds": generation_seconds,
                    "instance": metadata,
                    "solver": solver,
                    "solver_log": solver_log.name,
                }
            )

            if solver["status"] == "SAT":
                assignment = parse_cms_model(output)
                candidate_report = verify_graph_candidate(
                    columns,
                    assignment,
                    exhaustive_normalizer=True,
                )
                candidate_report["type"] = entry
                candidate_path = args.results / f"{prefix}_VERIFIED_CANDIDATE.json"
                atomic_json(candidate_path, candidate_report)
                record["candidate_report"] = candidate_path.name
                summary["sat_candidate"] = candidate_path.name
                summary["results"].append(record)
                atomic_json(summary_path, summary)
                # Preserve the exact instance and model for an independently
                # reproducible construction certificate.
                shutil.copy2(instance, args.results / instance.name)
                break
        except Exception as error:  # keep the shard auditable and resumable
            record.update(
                {
                    "status": "ERROR",
                    "error": repr(error),
                    "traceback": traceback.format_exc(),
                }
            )
            if instance.exists():
                preserved = args.results / f"{prefix}_error.cnf"
                shutil.copy2(instance, preserved)
                record["preserved_instance"] = preserved.name
        finally:
            if instance.exists() and summary.get("sat_candidate") is None:
                instance.unlink()

        summary["results"].append(record)
        atomic_json(summary_path, summary)

    summary.pop("current_type_id", None)
    summary["complete"] = summary.get("sat_candidate") is not None or len(summary["results"]) == len(assigned)
    atomic_json(summary_path, summary)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
