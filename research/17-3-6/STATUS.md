# [[17,3,6]] research status

This branch records work toward resolving existence of a binary stabilizer code with parameters `[[17,3,6]]`.

## Verified reductions so far

The current exact reductions imply that any candidate must be pure through weight five, Type I (odd), non-CSS, non-GF(4)-linear, noncyclic, and coordinate-asymmetric. Ordinary MacWilliams/shadow constraints leave seven integral profiles.

For the profile with `(S3,S4,S5,A6,A7)=(1,0,189,0,0)`, the unique weight-three global-shadow word can be normalized to `XXX I^14`. One-coordinate shortening then has exactly two forced enumerator types: three coordinates in the anchor support and fourteen outside it.

Pair-shortening and split-enumerator first-moment constraints remain feasible, so those relaxations alone do not close the profile.

## Current exact construction/nonexistence formulation

Extend a pure candidate to a self-dual additive parent. In graph form the parent is represented by a symmetric zero-diagonal 17x17 adjacency matrix Gamma. A logical quotient class represented by q has distance at least six from the parent exactly when every Pauli error of weight at most five has syndrome different from q.

For the profile-6 anchor, the graph must satisfy the exact shadow equation

`Gamma * t = 1 + degree(Gamma) (mod 2)`, with `t=(1,1,1,0,...,0)`.

The remaining search can therefore be phrased as an exact Boolean problem: find a distance-six self-dual graph parent satisfying that anchor and a three-dimensional syndrome subspace whose seven nonzero classes are all at coset distance at least six. If such a model is found it gives a construction; if the complete symmetry-reduced cases are UNSAT with checkable certificates it proves nonexistence.

## Integrity rule

No numerical optimizer status, stochastic failure, or interrupted solver run is to be called a solution. Closure requires either an independently verified generator matrix or an independently replayable exact nonexistence certificate.
