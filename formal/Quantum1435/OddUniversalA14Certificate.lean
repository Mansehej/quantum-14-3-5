import Quantum1435.OddUniversalSourceRows
import Mathlib.Tactic

/-!
# Arithmetic certificate for the first universal odd row

This certificate is isolated from both semantic definitions and the second
row so each large normalization runs in its own Lean process.
-/

namespace Quantum1435

/-- The first universal odd-branch row, derived as an explicit integer linear
combination of the source equations. -/
theorem oddUniversalA14_of_sourceRows (d : OddUniversalSourceRows) :
    d.A14 + 18 * d.A2 + 12 * d.A4 + 12 * d.A5 + 3 * d.A6 +
      4 * d.S2 + 2 * d.S4 = 36 := by
  have hscaled :
      1024 *
          (d.A14 + 144 * d.A1 + 18 * d.A2 + 54 * d.A3 +
            12 * d.A4 + 12 * d.A5 + 3 * d.A6 + 4 * d.S2 + 2 * d.S4) =
        1024 * 36 := by
    linear_combination
      63 * d.total + 30 * d.evenTotal + 18 * d.macWilliams1 +
        16 * d.macWilliams2 + 3 * d.macWilliams3 + 2 * d.macWilliams4 -
        2 * d.signedShadow2 - d.signedShadow4
  rw [d.a1Zero, d.a3Zero] at hscaled
  omega

end Quantum1435
