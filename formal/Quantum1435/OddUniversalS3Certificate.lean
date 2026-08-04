import Quantum1435.OddUniversalA14Certificate
import Mathlib.Tactic

/-!
# Arithmetic certificate for the second universal odd row

The strict import chain ensures that the first certificate is replayed from
its `.olean` while only this combination is elaborated.
-/

namespace Quantum1435

/-- The second universal odd-branch row, derived as an explicit integer linear
combination of the source equations. -/
theorem oddUniversalS3_of_sourceRows (d : OddUniversalSourceRows) :
    2 * d.S3 + 12 * d.A2 + 19 * d.A4 + 38 * d.A5 + 6 * d.A6 +
      36 * d.S2 + 8 * d.S4 = 105 := by
  have hscaled :
      2048 *
          (2 * d.S3 + 456 * d.A1 + 12 * d.A2 + 173 * d.A3 +
            19 * d.A4 + 38 * d.A5 + 6 * d.A6 + 36 * d.S2 + 8 * d.S4) =
        2048 * 105 := by
    linear_combination
      399 * d.total - 168 * d.evenTotal + 114 * d.macWilliams1 +
        78 * d.macWilliams2 + 17 * d.macWilliams3 + 11 * d.macWilliams4 -
        36 * d.signedShadow2 - 2 * d.signedShadow3 - 8 * d.signedShadow4
  rw [d.a1Zero, d.a3Zero] at hscaled
  omega

end Quantum1435
