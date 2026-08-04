import Quantum1435.P11Geometry
import Mathlib.Tactic

/-!
# Arithmetic behind the p03 normal forms

This file formalizes the coordinate-category part of the manuscript's p03
normal-form argument.  For two Pauli words `u,v`, coordinates in their joint
support are divided into four categories:

* `A`: `u` alone is nonzero;
* `B`: `v` alone is nonzero;
* `C`: both are nonzero with the same label;
* `D`: both are nonzero with different labels.

The three weights are `A+C+D`, `B+C+D`, and `A+B+D`.  Moreover, `D` modulo
two is the symplectic product.  Consequently, when all three nonzero words in
a rank-two plane have weight four, the only category counts are
`(p,p,p,4-2p)` for `p = 0,1,2`.

The local-Clifford and coordinate-permutation transport from these three
count patterns to the displayed representatives is deliberately not claimed
here.  This file also proves the semantic support-disjoint conclusion used
in the rank-three case once a pair sum is known to have weight eight.
-/

namespace Quantum1435

open scoped BigOperators

/-! ## Abstract category arithmetic -/

/-- The four coordinate-category counts for a rank-two weight-four plane. -/
structure RankTwoCategoryCounts where
  A : ℕ
  B : ℕ
  C : ℕ
  D : ℕ
  weightU : A + C + D = 4
  weightV : B + C + D = 4
  weightSum : A + B + D = 4
  dEven : Even D

/-- The three weight equations force the manuscript's parameterization.
The parity field records the commutation condition, although the three
natural-number equations already imply it. -/
theorem rankTwo_category_arithmetic (d : RankTwoCategoryCounts) :
    ∃ p : ℕ, (p = 0 ∨ p = 1 ∨ p = 2) ∧
      d.A = p ∧ d.B = p ∧ d.C = p ∧ d.D = 4 - 2 * p := by
  obtain ⟨k, hk⟩ := d.dEven
  have hU := d.weightU
  have hV := d.weightV
  have hSum := d.weightSum
  refine ⟨d.A, ?_, rfl, ?_, ?_, ?_⟩
  all_goals omega

/-- Equivalent closed enumeration of the three rank-two count patterns. -/
theorem rankTwo_category_trichotomy (d : RankTwoCategoryCounts) :
    (d.A = 0 ∧ d.B = 0 ∧ d.C = 0 ∧ d.D = 4) ∨
    (d.A = 1 ∧ d.B = 1 ∧ d.C = 1 ∧ d.D = 2) ∨
    (d.A = 2 ∧ d.B = 2 ∧ d.C = 2 ∧ d.D = 0) := by
  obtain ⟨p, hp, hA, hB, hC, hD⟩ := rankTwo_category_arithmetic d
  rcases hp with rfl | rfl | rfl <;> simp_all

/-! ## Semantic Pauli coordinate categories -/

/-- Number of coordinates on which only the first word is nonzero. -/
def p03CategoryA {n : ℕ} (u v : Pauli n) : ℕ :=
  (Finset.univ.filter fun i ↦ u i ≠ 0 ∧ v i = 0).card

/-- Number of coordinates on which only the second word is nonzero. -/
def p03CategoryB {n : ℕ} (u v : Pauli n) : ℕ :=
  (Finset.univ.filter fun i ↦ u i = 0 ∧ v i ≠ 0).card

/-- Number of coordinates carrying the same nonidentity label in both words. -/
def p03CategoryC {n : ℕ} (u v : Pauli n) : ℕ :=
  (Finset.univ.filter fun i ↦ u i ≠ 0 ∧ u i = v i).card

/-- Number of coordinates carrying two different nonidentity labels. -/
def p03CategoryD {n : ℕ} (u v : Pauli n) : ℕ :=
  (Finset.univ.filter fun i ↦ u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i).card

/-- The support of a phase-free Pauli word. -/
def p03Support {n : ℕ} (u : Pauli n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ u i ≠ 0

private theorem card_filter_eq_sum_indicator {n : ℕ}
    (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ i, if p i then 1 else 0 := by
  simp

/-- Over `F₂²`, two labels add to zero exactly when they coincide. -/
@[simp] theorem localPauli_add_eq_zero_iff (a b : F₂ × F₂) :
    a + b = 0 ↔ a = b := by
  rcases a with ⟨ax, az⟩
  rcases b with ⟨bx, bz⟩
  fin_cases ax <;> fin_cases az <;> fin_cases bx <;> fin_cases bz <;> decide

/-- On one coordinate, the symplectic product is one exactly for two
different nonidentity Pauli labels. -/
theorem localSymplectic_eq_differentIndicator (a b : F₂ × F₂) :
    a.1 * b.2 + a.2 * b.1 =
      if a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b then 1 else 0 := by
  rcases a with ⟨ax, az⟩
  rcases b with ⟨bx, bz⟩
  fin_cases ax <;> fin_cases az <;> fin_cases bx <;> fin_cases bz <;> decide

/-- Weight of the first word in terms of coordinate categories. -/
theorem pauliWeight_eq_categories_ACD {n : ℕ} (u v : Pauli n) :
    pauliWeight u = p03CategoryA u v + p03CategoryC u v + p03CategoryD u v := by
  classical
  unfold pauliWeight p03CategoryA p03CategoryC p03CategoryD
  rw [card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : u i = 0 <;> by_cases hv : v i = 0 <;>
    by_cases huv : u i = v i <;> simp_all

/-- Weight of the second word in terms of coordinate categories. -/
theorem pauliWeight_eq_categories_BCD {n : ℕ} (u v : Pauli n) :
    pauliWeight v = p03CategoryB u v + p03CategoryC u v + p03CategoryD u v := by
  classical
  unfold pauliWeight p03CategoryB p03CategoryC p03CategoryD
  rw [card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : u i = 0 <;> by_cases hv : v i = 0 <;>
    by_cases huv : u i = v i <;> simp_all

/-- Weight of the binary sum in terms of coordinate categories. -/
theorem pauliWeight_add_eq_categories_ABD {n : ℕ} (u v : Pauli n) :
    pauliWeight (u + v) =
      p03CategoryA u v + p03CategoryB u v + p03CategoryD u v := by
  classical
  unfold pauliWeight p03CategoryA p03CategoryB p03CategoryD
  rw [card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.add_apply]
  by_cases hu : u i = 0 <;> by_cases hv : v i = 0 <;>
    by_cases huv : u i = v i <;> simp_all

/-- The global symplectic product is the parity of category `D`. -/
theorem symplecticForm_eq_categoryD_cast {n : ℕ} (u v : Pauli n) :
    symplecticForm n u v = (p03CategoryD u v : F₂) := by
  classical
  have hsum := Finset.sum_boole (R := F₂)
    (fun i : Fin n ↦ u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i) Finset.univ
  change (∑ i, ((u i).1 * (v i).2 + (u i).2 * (v i).1)) =
    ((Finset.univ.filter fun i ↦
      u i ≠ 0 ∧ v i ≠ 0 ∧ u i ≠ v i).card : F₂)
  simp_rw [localSymplectic_eq_differentIndicator]
  exact hsum

/-- Commutation makes the different-nonidentity category even. -/
theorem categoryD_even_of_commute {n : ℕ} {u v : Pauli n}
    (hcomm : Commute u v) : Even (p03CategoryD u v) := by
  rw [Commute, symplecticForm_eq_categoryD_cast] at hcomm
  have hdiv : 2 ∣ p03CategoryD u v :=
    (ZMod.natCast_eq_zero_iff (p03CategoryD u v) 2).mp hcomm
  exact even_iff_two_dvd.mpr hdiv

/-- The abstract three-pattern result applied to actual commuting Pauli
words of weights four, four, and four. -/
theorem pauli_rankTwo_category_arithmetic {n : ℕ} {u v : Pauli n}
    (hu : pauliWeight u = 4) (hv : pauliWeight v = 4)
    (huv : pauliWeight (u + v) = 4) (hcomm : Commute u v) :
    ∃ p : ℕ, (p = 0 ∨ p = 1 ∨ p = 2) ∧
      p03CategoryA u v = p ∧ p03CategoryB u v = p ∧
      p03CategoryC u v = p ∧ p03CategoryD u v = 4 - 2 * p := by
  let d : RankTwoCategoryCounts :=
    { A := p03CategoryA u v
      B := p03CategoryB u v
      C := p03CategoryC u v
      D := p03CategoryD u v
      weightU := by
        rw [← hu]
        exact (pauliWeight_eq_categories_ACD u v).symm
      weightV := by
        rw [← hv]
        exact (pauliWeight_eq_categories_BCD u v).symm
      weightSum := by
        rw [← huv]
        exact (pauliWeight_add_eq_categories_ABD u v).symm
      dEven := categoryD_even_of_commute hcomm }
  exact rankTwo_category_arithmetic d

/-! ## Rank-three support geometry -/

/-- If both words have weight four and their sum has weight eight, their
supports are disjoint.  This is the semantic pairwise-support conclusion
used after the p03 coefficient argument rules out smaller even sum weights. -/
theorem p03_supports_disjoint_of_weight_add_eq_eight {n : ℕ} {u v : Pauli n}
    (hu : pauliWeight u = 4) (hv : pauliWeight v = 4)
    (huv : pauliWeight (u + v) = 8) :
    Disjoint (p03Support u) (p03Support v) := by
  classical
  have hU := pauliWeight_eq_categories_ACD u v
  have hV := pauliWeight_eq_categories_BCD u v
  have hUV := pauliWeight_add_eq_categories_ABD u v
  rw [hu] at hU
  rw [hv] at hV
  rw [huv] at hUV
  have hC : p03CategoryC u v = 0 := by omega
  have hD : p03CategoryD u v = 0 := by omega
  rw [Finset.disjoint_left]
  intro i hiU hiV
  have hiU' : u i ≠ 0 := by simpa [p03Support] using hiU
  have hiV' : v i ≠ 0 := by simpa [p03Support] using hiV
  by_cases heq : u i = v i
  · have himem : i ∈ Finset.univ.filter (fun j ↦ u j ≠ 0 ∧ u j = v j) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hiU', heq⟩⟩
    have hpos : 0 < p03CategoryC u v := by
      exact Finset.card_pos.mpr ⟨i, himem⟩
    omega
  · have himem : i ∈ Finset.univ.filter
        (fun j ↦ u j ≠ 0 ∧ v j ≠ 0 ∧ u j ≠ v j) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨hiU', hiV', heq⟩⟩
    have hpos : 0 < p03CategoryD u v := by
      exact Finset.card_pos.mpr ⟨i, himem⟩
    omega

end Quantum1435
