# Conceptual lemmas and executable boundary

This file states the small handwritten mathematical kernel used by the
proof; the accompanying paper presents the same material in full.  The
checker does not ask the reader to trust any target-specific count or
coefficient: those are regenerated.  It does rely on the elementary
coding-theory correspondences below.

Throughout, \(P=\mathbb F_2^{2n}\) is written \(v=(x\mid z)\), with

\[
\langle(x\mid z),(x'\mid z')\rangle_s=x\cdot z'+z\cdot x',
\qquad
q(x\mid z)=\operatorname{wt}(x\mid z)\pmod2.
\]

## LEMMA-STAB: binary stabilizer correspondence

After discarding Pauli phases, multiplication is vector addition in \(P\),
and two Paulis commute exactly when their symplectic product is zero.
Therefore an \(r\)-generator stabilizer with no hidden dependence is an
\(r\)-dimensional isotropic subspace \(C\).  Its commuting normalizer is
\(C^{\perp_s}\), and stabilizer elements themselves do not act logically.
Thus the code has \(k=n-r\) logical qubits and distance

\[
\min\{\operatorname{wt}(v):v\in C^{\perp_s}\setminus C\}.
\]

This proves that the argument covers degeneracy: a low-weight vector in \(C\)
is allowed, while a low-weight vector in \(C^{\perp_s}\setminus C\) is not.

## LEMMA-Q: Pauli weight is a quadratic refinement

At one coordinate, direct inspection of the 16 ordered pairs in
\(\{I,X,Y,Z\}^2\) gives

\[
q(u+v)=q(u)+q(v)+\langle u,v\rangle_s.
\]

Summing the local identity proves it on \(P\).  The primary checker repeats
all 16 cases.  On an isotropic subspace \(C\), the polar term vanishes, so
\(q|_C\) is linear.  If \(C\) contains an odd word, this functional is
nonzero and

\[
C_0=\ker(q|_C)
\]

has codimension one.  For the target, \(\dim C=11\) and \(\dim C_0=10\).

## LEMMA-MW: MacWilliams and shadow character sums

For any additive \(C\subseteq P\), character orthogonality gives

\[
1_{C^{\perp_s}}(v)=\frac1{|C|}
\sum_{c\in C}(-1)^{\langle c,v\rangle_s}.
\]

For fixed \(\operatorname{wt}(c)=i\), summing the character over all
weight-\(j\) Paulis gives

\[
K_j(i)=\sum_t(-1)^t3^{j-t}
\binom{i}{t}\binom{n-i}{j-t}.
\]

Consequently, for the weight enumerators \(A\) of \(C\) and \(B\) of
\(C^{\perp_s}\),

\[
B_j=\frac1{|C|}\sum_i A_iK_j(i).
\]

For odd \(C\), character orthogonality applied to the even kernel \(C_0\)
gives

\[
E_j=\frac1{|C_0|}\sum_{i\ {\rm even}}A_iK_j(i)
\]

for \(E=W_{C_0^{\perp_s}}\).  Since \(C^{\perp_s}\) has index two in
\(C_0^{\perp_s}\), their set difference

\[
\mathcal S=C_0^{\perp_s}\setminus C^{\perp_s}
\]

is the nontrivial affine coset and has enumerator \(S=E-B\).  Subtracting the
two transforms yields the shadow formula

\[
S_j=\frac1{|C|}\sum_i(-1)^iA_iK_j(i).
\]

In particular,

\[
\mathcal S+\mathcal S=C^{\perp_s},\qquad
\mathcal S+C^{\perp_s}=\mathcal S,
\]

and every shadow word commutes with \(C_0\).  These translation rules are the
only shadow-coset properties used by the collision arguments.

## LEMMA-EVEN: elimination of the all-even branch

By LEMMA-Q, \(q|_C\) is linear on the isotropic \(C\), so either \(C\)
contains an odd-weight word (the odd branch, with
\(\dim C_0=10\)) or every word of \(C\) is even.  This lemma closes the
second branch by MacWilliams counting and integrality alone; no extension,
shadow, or geometric machinery is needed.

Assume \(\dim C=11\), every weight of \(C\) even, and
\(\min\{\operatorname{wt}(v):v\in C^{\perp_s}\setminus C\}\ge5\).  The branch
hypothesis leaves the eight unknowns \(A_0,A_2,\dots,A_{14}\), and exactly
six affine equations hold:

1. \(A_0=1\) and \(\sum_iA_i=|C|=2^{11}=2048\);
2. by LEMMA-MW, \(2048\,B_j=\sum_iA_iK_j(i)\), and distance at least five
   forces \(B_j=A_j\) for \(1\le j\le4\): the inclusion
   \(C\subseteq C^{\perp_s}\) gives \(B_j\ge A_j\), while a word of
   \(C^{\perp_s}\setminus C\) of weight at most four would contradict the
   distance, so \(B_j\le A_j\).  Degeneracy is genuinely permitted here:
   \(A_2\) and \(A_4\) remain free unknowns of the system.

Exact rational row reduction leaves the two free parameters \(p=A_{12}\) and
\(q=A_{14}\) and expresses

\[
40A_2=-1145+p+6q,\qquad
10A_4=-35+p-14q,\qquad
20A_6=4965-13p+102q.
\]

Cross-eliminating \(p\) and \(q\) from the affine functions
\(1,A_2,A_4,A_6\) yields the single relation

\[
16A_2+9A_4+2A_6=7.
\]

Every coefficient is positive and every \(A_i\) is a nonnegative integer, so
\(16A_2\le7\) forces \(A_2=0\), then \(9A_4\le7\) forces \(A_4=0\), and
\(2A_6=7\) is impossible modulo two.  Hence no all-even eleven-dimensional
isotropic subspace attains distance five, and every candidate code lies in
the odd branch.

The primary checker regenerates the row reduction, the displayed
parameterization, and the relation exactly (`EVEN.RREF`,
`EVEN.CONTRADICTION`), and the exact-algebra checker rederives the same
relation independently.

## LEMMA-EXT: self-dual extensions and six-dimensional incidence

For the target,

\[
V=C^{\perp_s}/C
\]

is a nondegenerate six-dimensional symplectic space.  A self-dual additive
extension \(D\), with \(C\subset D=D^{\perp_s}\), corresponds exactly to a
three-dimensional totally isotropic subspace \(D/C\), i.e. a Lagrangian in
\(V\).

The executable enumeration finds all 135 Lagrangians and verifies that each
nonzero point lies in 15.  Hence a word of \(C\) belongs to all 135
extensions, while a word of \(C^{\perp_s}\setminus C\) belongs to 15.
Averaging their weight enumerators gives

\[
\overline N
=\frac{135A+15(B-A)}{135}
=\frac{8A+B}{9}.
\]

No group-transitivity count is merely inserted: both implementations
enumerate the incidence independently.

## LEMMA-QUOTIENT-SHADOW: the 30-incidence factor

The quotient

\[
W=C_0^{\perp_s}/C_0
\]

has symplectic dimension eight.  The quadratic form \(q\) descends to \(W\):
if \(v\in C_0^{\perp_s}\) and \(c\in C_0\), then
\(q(v+c)=q(v)\) by LEMMA-Q.

The ambient quadratic space is the orthogonal sum of 14 coordinate planes.
Each coordinate plane has Arf invariant one, so the ambient Arf invariant is
\(14\bmod 2=0\).  Here is the required Witt reduction explicitly.  Choose a
nonzero singular \(e\in C_0\).  Nondegeneracy supplies \(g\) with
\(\langle e,g\rangle_s=1\); if \(q(g)=1\), replace \(g\) by \(g+e\), which
has \(q(g+e)=0\).  For every remaining basis vector \(c\in C_0\) having
\(\langle c,g\rangle_s=1\), replace \(c\) by \(c+e\).  This leaves it
singular and makes it perpendicular to the hyperbolic plane
\(\langle e,g\rangle\).  Iterating through a basis of the 10-dimensional
\(C_0\) splits off ten singular hyperbolic planes.  Their Arf invariants are
zero, so the nonsingular 8-dimensional remainder has Arf invariant zero and
is plus type.  Therefore the quotient is isometric to

\[
q(x\mid z)=x\cdot z,\qquad (x,z)\in\mathbb F_2^4\oplus\mathbb F_2^4.
\]

The nonzero element \(r=C/C_0\) is anisotropic because its representatives
have odd weight.  A self-dual extension becomes a four-dimensional
symplectic Lagrangian \(D/C_0\) containing \(r\).

For a self-dual odd code \(D\), its shadow classes are precisely the affine
solutions

\[
\operatorname{Sh}(D)=
\{h\in W:\langle h,d\rangle_s=q(d)\text{ for every }d\in D/C_0\}.
\]

This follows from the character definition in LEMMA-MW: the displayed linear
functional specifies the nontrivial coset of the dual of the even kernel.

The primary checker now exhausts the entire canonical finite model.  It
finds:

- 135 Lagrangians containing \(r\);
- 16 shadow classes for each;
- all extension-shadow classes have \(q(h)=0\);
- 72 even classes satisfy \(\langle h,r\rangle_s=1\);
- each such class occurs in exactly 30 extension shadows;
- \(135\cdot16=72\cdot30=2160\).

It also generates the orthogonal-transvection orbit of \(r\) and obtains all
120 anisotropic vectors, so the selected representative is not a hidden
special case.

A global shadow word \(s\) maps to a class with
\(\langle s,r\rangle_s=1\).  If it has even weight, exactly 30 of the 135
extension shadows contain it; if it has odd weight, none does.  Therefore,
for the *global* shadow coefficients,

\[
\overline T_j=
\begin{cases}
\frac{30}{135}S_j=\frac29S_j,&j\text{ even},\\
0,&j\text{ odd}.
\end{cases}
\]

This explicit statement prevents the former global-versus-average notation
error: \(S_2,S_4\) are integers, while their extension-shadow averages are
\(2S_2/9,2S_4/9\).

## LEMMA-LC: normal-form operations

A coordinate permutation preserves weight, addition, and the symplectic
form.  On one qubit, a Clifford action permutes \(X,Y,Z\), and every
permutation in \(S_3\cong GL(2,2)\) occurs.  Independent such actions also
preserve weight and commutation.  Thus they may normalize a finite
configuration without changing any branch condition.

For the p03 branch, the checker does not assume representatives.  It
enumerates the five simultaneous local \(S_3\)-orbits of ordered Pauli
columns.  For a rank-two plane, let \(A,B,C,D\) count columns of types
\((a,I),(I,b),(a,a),(a,b)\) with \(a\ne b\ne I\).  Requiring all three
nonzero plane words to have weight four gives

\[
A+C+D=B+C+D=A+B+D=4.
\]

The exhaustive nonnegative solutions are
\((A,B,C,D)=(p,p,p,4-2p)\) for \(p=0,1,2\).  In the rank-three case, the
three independent weight-four words are all the weight-four words because
\(A_4=3\).  A pair sum is distinct from those three, so it cannot have weight
four; \(A_2=A_6=0\), and its weight is even and at most eight.  It must
therefore have weight eight, forcing each pair of supports to be disjoint.
These are exactly the four generated forms.

## LEMMA-COLLISION: shadow differences

If \(s,t\) are shadow words, LEMMA-MW gives
\(s+t\in C^{\perp_s}\).  Under distance at least five, a difference of weight
at most four must lie in \(C\).  The branch enumerators identify exactly
which such stabilizers exist.  If two weight-three words share a
coordinate-Pauli incidence, their difference has weight at most four; hence
it must be one of those explicitly enumerated weight-four stabilizers.

## LEMMA-P01-INCIDENCE: the 1, 42, and 36 bounds

In profile \((A_2,A_4)=(0,1)\), write \(u\) for the unique weight-four
stabilizer; also \(A_1=A_3=0\).

First, \(S_1\leq1\): two distinct weight-one shadow words would differ by a
normalizer word of weight at most two, which distance would put in \(C\),
contrary to \(A_1=A_2=0\).  If \(S_1=1\), its word \(h\) cannot coexist with
a weight-two shadow word, since their difference has weight at most three.
Thus \(S_2=0\).  For each weight-three shadow word \(g\), the difference
\(h+g\) has weight at most four and hence must equal \(u\); consequently
\(g=h+u\) is unique and \(S_3\leq1\).

Now suppose \(S_1=0\).  A pair of weight-three shadow words sharing a bin
must differ by \(u\).  After normalizing \(u\), the finite checker enumerates
all 90 such translation pairs, all \(\binom{90}{2}=4005\) pairs of pairs, and
finds no two compatible with the rule that every cross-difference is either
\(u\) or has weight at least five.  It also verifies that every translation
pair shares exactly one bin.  Hence the total repeated-bin occupancy excess
is at most one.  With 42 coordinate-Pauli bins and \(3S_3\) incidences,
\(3S_3-42\leq1\), so \(S_3\leq14\).

Finally suppose \(S_2=1\), with weight-two shadow word \(h\).  For any
weight-three shadow word \(g\), the normalizer word \(h+g\) has weight at most
five.  If its weight were at most four, it would have to equal \(u\).  But
\(u\in C_0\), while \(h\in C_0^{\perp_s}\), so LEMMA-Q gives
\(q(h+u)=q(h)+q(u)+\langle h,u\rangle_s=0\), contradicting the odd weight of
\(g\).  Therefore \(\operatorname{wt}(h+g)=5\), which is equivalent to
support disjointness.  Only the other 12 coordinates are available, giving
36 bins.  The same repeated-excess bound yields \(3S_3-36\leq1\), hence
\(S_3\leq12\).  Both implementations exhaust all 9,828 possible \(g\) and
verify that the algebraic weight-five condition is exactly support
disjointness.

The remaining p03 step uses four degree histograms and exhaustive lower and
upper collision bounds computed by independent checkers.

## Trust boundary

The handwritten obligations are the proofs above, especially the explicit
Witt reduction and the character interpretation of extension shadows.  The
code validates every finite consequence in the relevant dimensions but is
not a formalization of general finite quadratic-space theory.
