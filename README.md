# The optimal distance of fourteen-qubit stabilizer codes encoding three qubits

This repository accompanies the paper *The Optimal Distance of Fourteen-Qubit
Stabilizer Codes Encoding Three Qubits* ([`paper/main.tex`](paper/main.tex)).

The paper proves that no binary qubit stabilizer code with parameters
`[[14,3,5]]` exists, including degenerate codes. Together with the known
`[[14,3,4]]` constructions, this establishes that the optimal minimum distance
for `n = 14`, `k = 3` is exactly 4. This repository contains the complete exact
computational package supporting the proof.

## Replay

The proof replays offline with one command from the repository root.
It requires Python 3.11+ and Node.js 18+ and uses standard libraries only, with
no third-party package, external solver, or network access.

```bash
python3 -I proof/replay.py
```

This reruns five independently written checkers in fresh processes,
byte-compares their certificates against second runs, performs 35 exact
cross-comparisons between implementations, and runs the full test suite,
including 16 mutation fixtures whose corruptions must be rejected. The Python
calibration verifier enumerates the `2^6` and `2^17` normalizer elements of the
`[[5,1,3]]` and `[[14,3,4]]` examples, respectively. The independently written
JavaScript verifier scans direct Pauli errors through weight five.

All proof decisions are exact. Python uses arbitrary-precision integers and
`Fraction`; JavaScript values remain safe exact integers, with `BigInt` used
for exact divisions. No tolerance-based numerical decision is used. The
theorem-specific searches are exhaustive and deterministic. One fixed-seed
randomized regression test is used only for calibration; no proof conclusion
depends on randomness. The command writes an SHA-256 manifest covering every
proof source, fixture, frozen specification, critical calibration-verifier
file, and generated proof artifact, excluding the manifest itself.

## Build the paper

The manuscript has been tested with Tectonic 0.16.9. From the repository root:

```bash
tectonic --outdir paper paper/main.tex
```

The PDF is generated under `paper/` and intentionally ignored by Git. It is
not part of the proof replay or its byte-reproducibility claim.

## Layout

- [`paper/`](paper/): LaTeX source of the paper.
- [`proof/`](proof/): the proof package, including the handwritten lemmas
  ([`proof/LEMMAS.md`](proof/LEMMAS.md)), five independent checker
  implementations in two languages, the claims ledger, tests with mutation
  fixtures, and the generated certificates.
- [`SPECIFICATION.md`](SPECIFICATION.md): frozen mathematical and
  serialization conventions.
- [`verifier_a/`](verifier_a/): exhaustive binary-normalizer
  `[[n,k,d]]` verifier (Python), used for calibration.
- [`verifier_b/`](verifier_b/): independent direct-Pauli `[[n,k,d]]`
  verifier (JavaScript), used for calibration.

## License

The code and proof artifact are MIT licensed; see [`LICENSE`](LICENSE).
The manuscript is separately copyrighted by the author.
