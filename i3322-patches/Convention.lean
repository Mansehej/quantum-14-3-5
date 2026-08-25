import Mathlib

namespace I3322

abbrev Setting := Fin 3
abbrev DeterministicResponse := Setting → Bool

/-- The integer indicator of the deterministic outcome labelled `1`. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- The frozen Collins--Gisin probability convention, evaluated on deterministic data. -/
def i3322CG (a b : DeterministicResponse) : ℤ :=
  - bit (a 0) - 2 * bit (b 0) - bit (b 1)
    + bit (a 0) * bit (b 0)
    + bit (a 0) * bit (b 1)
    + bit (a 0) * bit (b 2)
    + bit (a 1) * bit (b 0)
    + bit (a 1) * bit (b 1)
    - bit (a 1) * bit (b 2)
    + bit (a 2) * bit (b 0)
    - bit (a 2) * bit (b 1)

/-- The Pál--Vértesi/Connor ordering used in the audited operator proof. -/
def i3322PV (a b : DeterministicResponse) : ℤ :=
  - bit (a 1) - bit (b 0) - 2 * bit (b 1)
    + bit (a 0) * bit (b 0)
    + bit (a 0) * bit (b 1)
    - bit (a 0) * bit (b 2)
    + bit (a 1) * bit (b 0)
    + bit (a 1) * bit (b 1)
    + bit (a 1) * bit (b 2)
    - bit (a 2) * bit (b 0)
    + bit (a 2) * bit (b 1)

/-- Swap settings 1 and 2 in one-based notation; setting 3 is fixed. -/
def swap12 (r : DeterministicResponse) : DeterministicResponse :=
  ![r 1, r 0, r 2]

/-- Exact convention concordance: there is no scale or additive shift. -/
theorem pv_eq_cg_after_swaps (a b : DeterministicResponse) :
    i3322PV a b = i3322CG (swap12 a) (swap12 b) := by
  cases ha0 : a 0 <;> cases ha1 : a 1 <;> cases ha2 : a 2 <;>
    cases hb0 : b 0 <;> cases hb1 : b 1 <;> cases hb2 : b 2 <;>
    norm_num [i3322PV, i3322CG, swap12, bit, ha0, ha1, ha2, hb0, hb1, hb2]

/-- Exhaustive kernel computation of the deterministic/local bound. -/
theorem deterministic_local_bound (a b : DeterministicResponse) :
    i3322CG a b ≤ 0 := by
  cases ha0 : a 0 <;> cases ha1 : a 1 <;> cases ha2 : a 2 <;>
    cases hb0 : b 0 <;> cases hb1 : b 1 <;> cases hb2 : b 2 <;>
    norm_num [i3322CG, bit, ha0, ha1, ha2, hb0, hb1, hb2]

/-- A deterministic strategy saturating the local bound. -/
def allZero : DeterministicResponse := fun _ => false

/-- The local bound is exactly zero, not merely at most zero. -/
theorem allZero_saturates : i3322CG allZero allZero = 0 := by
  decide

/-- The all-one strategy also saturates the frozen convention. -/
def allOne : DeterministicResponse := fun _ => true

theorem allOne_saturates : i3322CG allOne allOne = 0 := by
  decide

/-- A mutation omitting Alice's first marginal penalty. -/
def i3322MissingAliceMarginal (a b : DeterministicResponse) : ℤ :=
  i3322CG a b + bit (a 0)

/-- Mutation control: the omitted marginal changes the local bound. -/
theorem missingAliceMarginal_breaks_local_bound :
    i3322MissingAliceMarginal allOne allOne = 1 := by
  decide

end I3322
