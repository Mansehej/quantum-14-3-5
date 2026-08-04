import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# The p03 incidence lower bound

This file isolates the elementary counting argument behind the lower bound
in the p03 branch.  Twenty-four vertices, each incident with three of
forty-two bins, give seventy-two incidences.  If `n_b` is the occupancy of a
bin, then the number of ordered pairs occurring together in a bin is
`n_b * (n_b - 1)`.  The pointwise inequality

`2 * n_b ≤ 2 + n_b * (n_b - 1)`

therefore forces the total ordered-pair count to be at least sixty.

The theorem is deliberately generic: it does not depend on Pauli words,
shadow enumerators, a certificate, or a particular representation of bins.
-/

namespace Quantum1435

open scoped BigOperators

/-- Number of selected vertices incident with a fixed bin. -/
def incidenceOccupancy {Vertex Bin : Type*} [DecidableEq Vertex]
    (selected : Finset Vertex) (incident : Vertex → Bin → Prop)
    [DecidableRel incident] (bin : Bin) : ℕ :=
  (selected.filter fun vertex ↦ incident vertex bin).card

/-- The elementary pointwise inequality used in the p03 incidence count. -/
private theorem two_mul_le_two_add_mul_pred (n : ℕ) :
    2 * n ≤ 2 + n * (n - 1) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have htwo : 2 ≤ n := by omega
  have hmul : 2 * (n - 1) ≤ n * (n - 1) :=
    Nat.mul_le_mul_right (n - 1) htwo
  calc
    2 * n = 2 + 2 * (n - 1) := by omega
    _ ≤ 2 + n * (n - 1) := Nat.add_le_add_left hmul 2

/-- The resource-safe form of the p03 lower-bound calculation.

There are no assumptions about how often a pair of vertices may meet.  A
later semantic lemma may use an at-most-one-common-bin hypothesis to identify
this sum with the number of oriented shared-bin pairs. -/
theorem sixty_le_sum_incidenceOccupancy_mul_pred
    {Vertex Bin : Type*} [DecidableEq Vertex] [DecidableEq Bin]
    (selected : Finset Vertex) (bins : Finset Bin)
    (incident : Vertex → Bin → Prop) [DecidableRel incident]
    (hselected : selected.card = 24)
    (hbins : bins.card = 42)
    (hdegree : ∀ vertex ∈ selected,
      (bins.filter fun bin ↦ incident vertex bin).card = 3) :
    60 ≤ ∑ bin ∈ bins,
      incidenceOccupancy selected incident bin *
        (incidenceOccupancy selected incident bin - 1) := by
  have hdouble :
      (∑ vertex ∈ selected,
          (bins.filter fun bin ↦ incident vertex bin).card) =
        ∑ bin ∈ bins, incidenceOccupancy selected incident bin := by
    simpa [incidenceOccupancy, Finset.bipartiteAbove,
      Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := incident) (s := selected) (t := bins))
  have hleft :
      (∑ vertex ∈ selected,
          (bins.filter fun bin ↦ incident vertex bin).card) = 72 := by
    calc
      (∑ vertex ∈ selected,
          (bins.filter fun bin ↦ incident vertex bin).card) =
          ∑ _vertex ∈ selected, 3 := Finset.sum_congr rfl hdegree
      _ = 72 := by simp [hselected]
  have hoccupancy :
      (∑ bin ∈ bins, incidenceOccupancy selected incident bin) = 72 := by
    rw [← hdouble]
    exact hleft
  have hsum :
      2 * (∑ bin ∈ bins, incidenceOccupancy selected incident bin) ≤
        bins.card * 2 +
          ∑ bin ∈ bins,
            incidenceOccupancy selected incident bin *
              (incidenceOccupancy selected incident bin - 1) := by
    calc
      2 * (∑ bin ∈ bins, incidenceOccupancy selected incident bin) =
          ∑ bin ∈ bins, 2 * incidenceOccupancy selected incident bin := by
            rw [Finset.mul_sum]
      _ ≤ ∑ bin ∈ bins,
          (2 + incidenceOccupancy selected incident bin *
            (incidenceOccupancy selected incident bin - 1)) := by
            exact Finset.sum_le_sum fun bin _ ↦
              two_mul_le_two_add_mul_pred
                (incidenceOccupancy selected incident bin)
      _ = bins.card * 2 +
          ∑ bin ∈ bins,
            incidenceOccupancy selected incident bin *
              (incidenceOccupancy selected incident bin - 1) := by
            rw [Finset.sum_add_distrib]
            simp
  rw [hoccupancy, hbins] at hsum
  omega

end Quantum1435
