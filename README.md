# There is no `[[14,3,5]]` quantum stabilizer code

Supplementary artifact for the paper *There is no [[14,3,5]] quantum
stabilizer code* ([`paper/main.tex`](paper/main.tex)).

The paper proves that no binary qubit stabilizer code with parameters
`[[14,3,5]]` exists, degenerate codes included: no 11-dimensional isotropic
subspace of F₂²⁸ has minimum symplectic-dual-coset weight at least five.
Consequently the optimal minimum distance for `n = 14`, `k = 3` is exactly
4.  This repository contains the complete machine verification behind the
paper.

## Replay

The entire proof replays offline with one command from the repository root
(Python 3.11+ and Node.js 18+, standard libraries only — no third-party
packages, no solver, no floating point, no network):

```bash
python3 -I proof/replay.py
```

This reruns five independently written checkers in fresh processes,
byte-compares their certificates against second runs, performs 35 exact
cross-comparisons between implementations, runs the full test suite
including 16 mutation fixtures (every compared claims region, corrupted,
must be rejected), executes both calibration verifiers on the `[[5,1,3]]`
and `[[14,3,4]]` codes by exhaustive enumeration, and writes an SHA-256
manifest over every source and output.

## Layout

- [`paper/`](paper/) — LaTeX source of the paper.
- [`proof/`](proof/) — the proof package: the handwritten lemmas
  ([`proof/LEMMAS.md`](proof/LEMMAS.md)), five independent checker
  implementations in two languages, the claims ledger, tests with mutation
  fixtures, and the generated certificates.
- [`SPECIFICATION.md`](SPECIFICATION.md) — frozen mathematical and
  serialization conventions.
- [`verifier_a/`](verifier_a/) — exhaustive binary-normalizer
  `[[n,k,d]]` verifier (Python), used for calibration.
- [`verifier_b/`](verifier_b/) — independent direct-Pauli `[[n,k,d]]`
  verifier (JavaScript), used for calibration.

## License

MIT — see [`LICENSE`](LICENSE).
