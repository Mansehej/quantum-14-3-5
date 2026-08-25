import Mathlib

namespace I3322

/-- The union of Alice and Bob finite spectral supports has cardinality at most the sum. -/
theorem spectral_union_card_le_sum
    {α : Type*} [DecidableEq α]
    (alice bob : Finset α) (dA dB : ℕ)
    (hA : alice.card ≤ dA) (hB : bob.card ≤ dB) :
    (alice ∪ bob).card ≤ dA + dB := by
  calc
    (alice ∪ bob).card ≤ alice.card + bob.card := Finset.card_union_le alice bob
    _ ≤ dA + dB := Nat.add_le_add hA hB

/-- A finite scalar support summary for a strategy value. -/
structure FiniteSpectralSummary (supportValue : Finset ℝ → ℝ) where
  aliceSupport : Finset ℝ
  bobSupport : Finset ℝ
  value : ℝ
  value_le_support : value ≤ supportValue (aliceSupport ∪ bobSupport)

/-- Strict finite-support obstruction for a scalar variational functional. -/
def NoFiniteSupportOptimizer (supportValue : Finset ℝ → ℝ) (beta : ℝ) : Prop :=
  ∀ support, supportValue support < beta

/-- Once a value-preserving finite spectral summary is supplied, finite-support rigidity
immediately gives a strict strategy bound. -/
theorem finite_summary_strictly_below
    {supportValue : Finset ℝ → ℝ} {beta : ℝ}
    (hNoFinite : NoFiniteSupportOptimizer supportValue beta)
    (summary : FiniteSpectralSummary supportValue) :
    summary.value < beta := by
  exact lt_of_le_of_lt summary.value_le_support
    (hNoFinite (summary.aliceSupport ∪ summary.bobSupport))

/-- The same reduction with explicit local-dimension support bounds. -/
theorem finite_summary_support_card_bound
    {supportValue : Finset ℝ → ℝ}
    (summary : FiniteSpectralSummary supportValue)
    (dA dB : ℕ)
    (hA : summary.aliceSupport.card ≤ dA)
    (hB : summary.bobSupport.card ≤ dB) :
    (summary.aliceSupport ∪ summary.bobSupport).card ≤ dA + dB := by
  classical
  exact spectral_union_card_le_sum
    summary.aliceSupport summary.bobSupport dA dB hA hB

/-- Mutation control: replacing the sum of local support bounds by their maximum is false. -/
theorem max_instead_of_sum_counterexample :
    (({0} : Finset ℕ) ∪ ({1} : Finset ℕ)).card > max 1 1 := by
  decide

end I3322
