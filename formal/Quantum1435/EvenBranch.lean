import Quantum1435.Parity
import Mathlib.Tactic

/-!
# The all-even enumerator certificate

This file formalizes the exact integer certificate used to eliminate the
all-even branch.  It does not trust the generated JSON or either executable
checker: the Krawtchouk coefficients and the linear combination are checked
again by Lean.

This arithmetic module exposes the five semantic rows as an interface.
`EvenSemantic`, `LocalKrawtchouk`, and `AllEvenComplete` discharge that
interface for actual all-even candidates.
-/

namespace Quantum1435

/-- The quaternary Krawtchouk polynomial used for additive Pauli codes. -/
def quantumKrawtchouk (n j i : ℕ) : ℤ :=
  ∑ s ∈ Finset.range (j + 1),
    (-1 : ℤ) ^ s * 3 ^ (j - s) * (Nat.choose i s : ℤ) *
      (Nat.choose (n - i) (j - s) : ℤ)

/-- The coefficient after imposing `B_j = A_j` and multiplying the
MacWilliams equation by `|C| = 2048`. -/
def evenDistanceCoefficient (j i : ℕ) : ℤ :=
  quantumKrawtchouk 14 j i - if i = j then 2048 else 0

/-- Closed kernel check of every coefficient used below. -/
theorem evenDistanceCoefficient_rows :
    (List.map (evenDistanceCoefficient 1) [2, 4, 6, 8, 10, 12, 14] =
      [34, 26, 18, 10, 2, -6, -14]) ∧
    (List.map (evenDistanceCoefficient 2) [2, 4, 6, 8, 10, 12, 14] =
      [-1525, 291, 123, 19, -21, 3, 91]) ∧
    (List.map (evenDistanceCoefficient 3) [2, 4, 6, 8, 10, 12, 14] =
      [4788, 1796, 340, -92, -12, 68, -364]) ∧
    (List.map (evenDistanceCoefficient 4) [2, 4, 6, 8, 10, 12, 14] =
      [28809, 4313, -87, -263, 201, -231, 1001]) := by
  decide

/-- The seven nontrivial coefficients of an all-even length-14 weight
enumerator, together with the five exact rows used by the proof.

`total` has `A₀ = 1` moved to the right.  Likewise, each `row*` has the
known Krawtchouk contribution of `A₀` moved to the right. -/
structure EvenEnumeratorCertificate where
  A2 : ℕ
  A4 : ℕ
  A6 : ℕ
  A8 : ℕ
  A10 : ℕ
  A12 : ℕ
  A14 : ℕ
  total :
    (A2 : ℤ) + A4 + A6 + A8 + A10 + A12 + A14 = 2047
  row1 :
    34 * (A2 : ℤ) + 26 * A4 + 18 * A6 + 10 * A8 + 2 * A10 -
      6 * A12 - 14 * A14 = -42
  row2 :
    -1525 * (A2 : ℤ) + 291 * A4 + 123 * A6 + 19 * A8 - 21 * A10 +
      3 * A12 + 91 * A14 = -819
  row3 :
    4788 * (A2 : ℤ) + 1796 * A4 + 340 * A6 - 92 * A8 - 12 * A10 +
      68 * A12 - 364 * A14 = -9828
  row4 :
    28809 * (A2 : ℤ) + 4313 * A4 - 87 * A6 - 263 * A8 + 201 * A10 -
      231 * A12 + 1001 * A14 = -81081

/-- Soundness of the explicit row certificate.

The integer multipliers are `(77, 38, 14, 5, 1)`.  Their combination of
the five source rows is `2048 * (16 A₂ + 9 A₄ + 2 A₆) = 2048 * 7`.
No external computation is trusted in this theorem. -/
theorem evenEnumeratorCertificate_relation (c : EvenEnumeratorCertificate) :
    16 * c.A2 + 9 * c.A4 + 2 * c.A6 = 7 := by
  have hscaled :
      2048 * (16 * (c.A2 : ℤ) + 9 * c.A4 + 2 * c.A6) = 2048 * 7 := by
    linear_combination
      77 * c.total + 38 * c.row1 + 14 * c.row2 + 5 * c.row3 + c.row4
  omega

/-- The all-even integer certificate is inconsistent with nonnegative word
counts. -/
theorem noEvenEnumeratorCertificate : ¬ Nonempty EvenEnumeratorCertificate := by
  rintro ⟨c⟩
  have h := evenEnumeratorCertificate_relation c
  omega

end Quantum1435
