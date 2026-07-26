# Verifier B: independent Pauli-string stabilizer verifier

Verifier B checks a binary qubit stabilizer directly in the alphabet
`I`, `X`, `Y`, `Z`. It has no dependency on Verifier A, does not import an
`[X|Z]` implementation, uses only the Node.js standard library, and does not
search for codes.

The checker is intended for exact certificates of the form one phase-free
Pauli generator per line. Blank lines and lines beginning with `#` are ignored.
All non-comment rows must have the same length.

## What it checks

1. Every generator pair commutes, using the parity of positions occupied by
   distinct non-identity Paulis.
2. All `2^m` phase-free subset products are enumerated. The generator rank is
   `log2(unique products)`, so dependence is detected by a collision.
3. For a commuting list, `k = n - generatorRank`.
4. Every Pauli error through the requested weight is generated
   support-by-support in deterministic order. An error is classified as:
   - non-normalizing if it anticommutes with a generator;
   - a stabilizer if it commutes and occurs in the enumerated product set;
   - a logical if it commutes and is absent from that set.
5. An exact-distance claim `d` passes only when there are no logicals of
   weights `0,...,d-1` and at least one logical at weight `d`.

Counts are for phase-free Pauli strings. Global phases do not affect binary
rank, commutation, stabilizer membership, Pauli weight, or code distance.

## Requirements and commands

Node.js 18 or newer is sufficient. There is no install step.

```sh
cd verifier_b
npm test
npm run test:deterministic
npm run verify:5
npm run verify:14
```

To check a proposed exact `[[14,3,5]]` certificate:

```sh
node src/cli.js candidate.pauli \
  --max-weight 5 --expect-n 14 --expect-k 3 --expect-distance 5
```

The CLI emits deterministic JSON and exits zero only when the requested exact
parameters pass. Without `--expect-*`, it exits zero for an independent,
pairwise-commuting stabilizer list. Structural failures exit one; malformed
input or arguments exit two.

## Regression fixtures

- `fixtures/5_1_3.pauli`: standard cyclic `[[5,1,3]]` code.
- `fixtures/14_3_4.pauli`: independent manual Pauli transcription of the
  code-table `[[14,3,4]]` matrix. See `TRANSCRIPTION_AUDIT.md`.
- `fixtures/duplicate_generator.pauli`: dependent-row corruption.
- `fixtures/anticommuting_symbol.pauli`: one-symbol anticommutation corruption.
- `fixtures/low_weight_logical.pauli`: valid code with a weight-one logical.
- `fixtures/degenerate_membership.pauli`: `[[5,1,3]]` plus a stabilized ancilla;
  its weight-one normalizer element is a stabilizer and must not be reported as
  a logical.

The regression suite also checks the Pauli multiplication and commutation
rules directly. Frozen outputs are under `logs/`.

## Independently reproduced results

| Fixture | rank | commuting | k | minimum logical | first witness |
| --- | ---: | --- | ---: | ---: | --- |
| `5_1_3.pauli` | 4 | yes | 1 | 3 | `XYXII` |
| `14_3_4.pauli` | 11 | yes | 3 | 4 | `XXXXIIIIIIIIII` |
| `degenerate_membership.pauli` | 5 | yes | 1 | 3 | deterministic test only |

For the table code, exact phase-free counts through weight five are:

| weight | all errors | commuting | stabilizers | logicals |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 1 | 0 |
| 1 | 42 | 2 | 2 | 0 |
| 2 | 819 | 1 | 1 | 0 |
| 3 | 9,828 | 0 | 0 | 0 |
| 4 | 81,081 | 105 | 0 | 105 |
| 5 | 486,486 | 594 | 6 | 588 |

The two weight-one commuting operators in that published fixture are its last
two stabilizer generators. Their membership is correctly distinguished from a
low-weight logical failure.

## Scope and ambiguities

- This checker validates a supplied certificate; it makes no claim that an
  `[[14,3,5]]` certificate exists.
- A bounded scan proves exact distance only through the largest scanned weight.
  The expected-distance checker therefore refuses a claim when weight `d` was
  not scanned.
- A redundant commuting generator list still defines a subgroup mathematically,
  but `validStabilizer` is false because the target specification requires a
  full-row-rank generator matrix.
- Input phases are deliberately omitted. For an independent isotropic binary
  generator space, phase choices do not change the distance calculation.
- The first logical witness is deterministic: supports are lexicographic, then
  non-identity symbols are ordered `X`, `Y`, `Z`.
- The source table states its matrix as `[X|Z]`; the transcription uses
  `(0,0)=I`, `(1,0)=X`, `(0,1)=Z`, `(1,1)=Y`. This convention is frozen in
  `TRANSCRIPTION_AUDIT.md` rather than implemented as a converter here.
