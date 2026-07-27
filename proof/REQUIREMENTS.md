# Runtime and dependency requirements

The proof code has no third-party dependencies.

- Python: 3.11 or newer; tested in the saved replay with Python 3.12.3.
- Node.js: 18 or newer; tested with Node v22.22.0.
- npm is neither invoked nor required.  No package-manager command is run.
- Python modules used by the proof are all standard library modules.
- Node runs the independently authored `cleanroom_checker.js` collision/orbit
  cross-check and the already independent `verifier_b` calibration suite;
  neither has package dependencies.

Proof-critical Python calculations use arbitrary-precision `int` and
`fractions.Fraction`. The JavaScript checker uses `Number` only within the safe
exact-integer range and uses `BigInt` for exact divisions. No tolerance-based
numerical decision is made. The theorem-specific searches are exhaustive and
deterministic. A fixed-seed randomized regression test is confined to verifier
calibration; no proof conclusion depends on randomness. No numerical
optimizer, SAT/SMT solver, wall clock, locale-dependent ordering, or network
response enters a proof conclusion.

The supported deterministic command is:

```bash
python3 -I proof/replay.py
```

`-I` isolates Python from user site configuration and environment path
injection.  The replay rejects optimized or non-isolated Python, scrubs child
process environments, and directs every Python child to a newly created
bytecode-cache prefix.  Thus a pre-existing repository or user cache cannot
supply imported proof code.  Every result-producing checker and test suite is
launched as a fresh subprocess.
