# Frozen specification

Frozen: 2026-07-24

## Target

Let

\[
H=[X\mid Z]\in\mathbb F_2^{11\times 28},
\]

where columns `0..13` are the `X` bits for qubits `1..14`, and columns
`14..27` are the correspondingly ordered `Z` bits.  Let

\[
\Lambda=\begin{pmatrix}0&I_{14}\\I_{14}&0\end{pmatrix}
\quad\text{and}\quad
C=\operatorname{rowspan}_{\mathbb F_2}(H).
\]

The required conditions are:

1. `rank(H) = 11`;
2. \(H\Lambda H^T=0\), so \(C\subseteq C^{\perp_s}\);
3. \(k=14-\dim C=3\);
4. with
   \[
   \operatorname{wt}(x\mid z)
   =|\{i:(x_i,z_i)\ne(0,0)\}|,
   \]
   the exact distance is
   \[
   d=\min\{\operatorname{wt}(v):v\in C^{\perp_s}\setminus C\}=5.
   \]

Thus all commuting Pauli vectors of weights one through four must be in `C`,
and at least one commuting vector outside `C` must have weight five.

## Scope and conventions

- This is a binary additive **qubit stabilizer** code.
- Degeneracy is allowed.  A stabilizer vector of weight below five does not
  lower the distance.
- No purity assumption is made.
- No `GF(4)`-linearity assumption is made.  In particular, binary dimension
  eleven is odd and cannot itself be a `GF(4)`-linear dimension.
- Pauli phases are discarded in the binary symplectic representation.
- The coordinate map is
  `(x,z) = 00 -> I, 10 -> X, 01 -> Z, 11 -> Y`.
- Nonadditive, subsystem, entanglement-assisted, qudit, and approximate codes
  are outside the target.
- A table lower bound written as five normally means a construction of
  distance at least five.  Exact distance still requires a weight-five logical
  witness unless a separately audited upper bound \(d\le5\) is invoked.

## Positive certificate

A complete positive certificate consists of a literal `11 x 28` bit matrix
plus independent checks of:

- shape and binary entries;
- rank eleven;
- zero symplectic Gram matrix;
- normalizer dimension seventeen;
- no vector in \(C^{\perp_s}\setminus C\) of weights one through four; and
- a displayed vector in \(C^{\perp_s}\setminus C\) of weight five.

At least two implementations using distinct representations and enumeration
paths must agree.

## Negative certificate

A complete negative certificate must cover every eleven-dimensional isotropic
binary subspace of \(\mathbb F_2^{28}\), including degenerate and asymmetric
ones.  It must include:

- the full search space and a proof that the encoding is equivalent to it;
- proofs for every symmetry reduction and case split;
- a complete case manifest;
- replayable proof objects; and
- a substantially smaller, independently audited checker.

A solver's `UNSAT` line, an exhausted ansatz, or a search without a coverage
proof is partial only.

## Safe designated-witness normalization

For the exact-distance-five question, choose a minimum logical Pauli vector.
A qubit permutation moves its five-qubit support to qubits `1..5`.
Independent one-qubit Clifford transformations map each nonidentity factor to
`Z`, preserving Pauli weight, commutation, stabilizer membership, and distance.
Therefore a complete exact-distance-five search may designate

\[
L=Z_1Z_2Z_3Z_4Z_5I_6\cdots I_{14}.
\]

It must enforce both \(L\in C^{\perp_s}\) and \(L\notin C\).  The first
condition says every stabilizer row has even `X` parity on qubits `1..5`.
This normalization does **not** justify any additional residual-symmetry
pruning without a separate orbit-coverage proof.
