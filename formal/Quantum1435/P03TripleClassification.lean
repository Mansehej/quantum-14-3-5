import Quantum1435.P03NormalForms

/-!
# Invariant classification of the three p03 weight-four words

This file extracts the three actual weight-four stabilizer words from the
coefficient equation `A₄ = 3` and classifies them without choosing
coordinates or Pauli labels. In the dependent case the existing category
arithmetic gives the three rank-two patterns. Otherwise every pair sum has
weight eight, so the three supports are pairwise disjoint.
-/

namespace Quantum1435

/-- A coefficient equal to three supplies three distinct words and an
exhaustive description of that weight class. -/
theorem exists_three_of_weightDistribution_eq_three {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (h : weightDistribution S j = 3) :
    ∃ u v w : Pauli n, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      ∀ x, x ∈ S ∧ pauliWeight x = j ↔
        x = u ∨ x = v ∨ x = w := by
  classical
  let words : Finset (Pauli n) :=
    Finset.univ.filter fun x : Pauli n ↦ x ∈ S ∧ pauliWeight x = j
  have hcard : words.card = 3 := by
    simpa [words, weightDistribution] using h
  obtain ⟨u, v, w, huv, huw, hvw, hwords⟩ :=
    Finset.card_eq_three.mp hcard
  refine ⟨u, v, w, huv, huw, hvw, ?_⟩
  intro x
  have hmem : x ∈ words ↔ x ∈ S ∧ pauliWeight x = j := by
    simp [words]
  rw [← hmem, hwords]
  simp

/-- The invariant alternatives for three distinct commuting weight-four
Pauli words. -/
inductive P03TripleGeometry (u v w : Pauli 14) : Prop
  | rankTwo0
      (sum_eq : u + v = w)
      (categoryA : p03CategoryA u v = 0)
      (categoryB : p03CategoryB u v = 0)
      (categoryC : p03CategoryC u v = 0)
      (categoryD : p03CategoryD u v = 4)
  | rankTwo1
      (sum_eq : u + v = w)
      (categoryA : p03CategoryA u v = 1)
      (categoryB : p03CategoryB u v = 1)
      (categoryC : p03CategoryC u v = 1)
      (categoryD : p03CategoryD u v = 2)
  | rankTwo2
      (sum_eq : u + v = w)
      (categoryA : p03CategoryA u v = 2)
      (categoryB : p03CategoryB u v = 2)
      (categoryC : p03CategoryC u v = 2)
      (categoryD : p03CategoryD u v = 0)
  | rankThree
      (disjointUV : Disjoint (p03Support u) (p03Support v))
      (disjointUW : Disjoint (p03Support u) (p03Support w))
      (disjointVW : Disjoint (p03Support v) (p03Support w))

/-- If a weight coefficient vanishes, no member of the submodule has that
weight. -/
theorem pauliWeight_ne_of_weightDistribution_eq_zero {n j : ℕ}
    (S : Submodule F₂ (Pauli n))
    (hzero : weightDistribution S j = 0)
    {x : Pauli n} (hxS : x ∈ S) : pauliWeight x ≠ j := by
  classical
  intro hxWeight
  have hxmem : x ∈ Finset.univ.filter
      (fun y : Pauli n ↦ y ∈ S ∧ pauliWeight y = j) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, ⟨hxS, hxWeight⟩⟩
  have hpos : 0 < (Finset.univ.filter
      (fun y : Pauli n ↦ y ∈ S ∧ pauliWeight y = j)).card :=
    Finset.card_pos.mpr ⟨x, hxmem⟩
  have hcard : (Finset.univ.filter
      (fun y : Pauli n ↦ y ∈ S ∧ pauliWeight y = j)).card = 0 := by
    simpa [weightDistribution] using hzero
  omega

/-- Every binary Pauli vector is its own additive inverse. -/
@[simp] theorem pauli_add_self_eq_zero {n : ℕ} (u : Pauli n) :
    u + u = 0 := by
  funext i
  change u i + u i = (0 : F₂ × F₂)
  exact CharTwo.add_self_eq_zero (u i)

/-- In the binary Pauli space, a sum vanishes exactly when its two summands
coincide. -/
theorem pauli_add_eq_zero_iff_eq {n : ℕ} (u v : Pauli n) :
    u + v = 0 ↔ u = v := by
  constructor
  · intro hzero
    funext i
    apply (localPauli_add_eq_zero_iff (u i) (v i)).mp
    have hi := congrFun hzero i
    simpa using hi
  · rintro rfl
    exact pauli_add_self_eq_zero u

private theorem add_third_relation_of_left {n : ℕ} {u v w : Pauli n}
    (h : u + w = v) : u + v = w := by
  calc
    u + v = u + (u + w) := congrArg (fun x ↦ u + x) h.symm
    _ = (u + u) + w := by rw [← add_assoc]
    _ = w := by rw [pauli_add_self_eq_zero, zero_add]

private theorem add_third_relation_of_right {n : ℕ} {u v w : Pauli n}
    (h : v + w = u) : u + v = w := by
  calc
    u + v = (v + w) + v := congrArg (fun x ↦ x + v) h.symm
    _ = (v + v) + w := by ac_rfl
    _ = w := by rw [pauli_add_self_eq_zero, zero_add]

/-- Two distinct commuting weight-four words have weight-eight sum once
weights two and six vanish and their sum is not the third weight-four word. -/
private theorem p03_pair_sum_weight_eight {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (hA2 : weightDistribution S 2 = 0)
    (hA6 : weightDistribution S 6 = 0)
    {a b c : Pauli n}
    (haS : a ∈ S) (hbS : b ∈ S)
    (haWeight : pauliWeight a = 4)
    (hbWeight : pauliWeight b = 4)
    (hab : a ≠ b)
    (hexhaust : ∀ x, x ∈ S ∧ pauliWeight x = 4 →
      x = a ∨ x = b ∨ x = c)
    (hsum_ne_c : a + b ≠ c) :
    pauliWeight (a + b) = 8 := by
  have habS : a + b ∈ S := S.add_mem haS hbS
  have hupper := pauliWeight_add_le a b
  rw [haWeight, hbWeight] at hupper
  have hparity : (pauliWeight (a + b) : F₂) = 0 := by
    rw [← pauliParity_eq_weight_cast, pauliParity_add, hiso haS hbS,
      pauliParity_eq_weight_cast, pauliParity_eq_weight_cast,
      haWeight, hbWeight]
    decide
  have heven : 2 ∣ pauliWeight (a + b) :=
    (ZMod.natCast_eq_zero_iff (pauliWeight (a + b)) 2).mp hparity
  have hne0 : pauliWeight (a + b) ≠ 0 := by
    intro hzero
    have habzero : a + b = 0 := pauliWeight_eq_zero_iff.mp hzero
    exact hab ((pauli_add_eq_zero_iff_eq a b).mp habzero)
  have hne2 : pauliWeight (a + b) ≠ 2 :=
    pauliWeight_ne_of_weightDistribution_eq_zero S hA2 habS
  have hne6 : pauliWeight (a + b) ≠ 6 :=
    pauliWeight_ne_of_weightDistribution_eq_zero S hA6 habS
  have hne4 : pauliWeight (a + b) ≠ 4 := by
    intro hfour
    rcases hexhaust (a + b) ⟨habS, hfour⟩ with ha | hb | hc
    · have hbzero : b = 0 := by
        apply add_left_cancel (a := a)
        simpa [add_assoc] using ha
      have hbWeightZero : pauliWeight b = 0 :=
        pauliWeight_eq_zero_iff.mpr hbzero
      omega
    · have hazero : a = 0 := by
        apply add_right_cancel (b := b)
        simpa [add_assoc] using hb
      have haWeightZero : pauliWeight a = 0 :=
        pauliWeight_eq_zero_iff.mpr hazero
      omega
    · exact hsum_ne_c hc
  omega

/-- Three distinct exhaustive weight-four words in the p03 profile have one
of the three rank-two category patterns, or have pairwise disjoint support. -/
theorem p03_classify_weightFour_triple
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (hA2 : weightDistribution S 2 = 0)
    (hA6 : weightDistribution S 6 = 0)
    {u v w : Pauli 14}
    (huS : u ∈ S) (hvS : v ∈ S) (hwS : w ∈ S)
    (huWeight : pauliWeight u = 4)
    (hvWeight : pauliWeight v = 4)
    (hwWeight : pauliWeight w = 4)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hexhaust : ∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
      x = u ∨ x = v ∨ x = w) :
    P03TripleGeometry u v w := by
  by_cases hsum : u + v = w
  · obtain ⟨p, hp, hA, hB, hC, hD⟩ :=
      pauli_rankTwo_category_arithmetic huWeight hvWeight
        (by simpa [hsum] using hwWeight) (hiso huS hvS)
    rcases hp with rfl | rfl | rfl
    · exact P03TripleGeometry.rankTwo0 hsum hA hB hC (by simpa using hD)
    · exact P03TripleGeometry.rankTwo1 hsum hA hB hC (by simpa using hD)
    · exact P03TripleGeometry.rankTwo2 hsum hA hB hC (by simpa using hD)
  · have hsumUW : u + w ≠ v := by
      intro h
      exact hsum (add_third_relation_of_left h)
    have hsumVW : v + w ≠ u := by
      intro h
      exact hsum (add_third_relation_of_right h)
    have huvWeight : pauliWeight (u + v) = 8 :=
      p03_pair_sum_weight_eight S hiso hA2 hA6
        huS hvS huWeight hvWeight huv
        (fun x hx ↦ (hexhaust x).mp hx) hsum
    have huwWeight : pauliWeight (u + w) = 8 :=
      p03_pair_sum_weight_eight S hiso hA2 hA6
        huS hwS huWeight hwWeight huw
        (fun x hx ↦ by
          rcases (hexhaust x).mp hx with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)) hsumUW
    have hvwWeight : pauliWeight (v + w) = 8 :=
      p03_pair_sum_weight_eight S hiso hA2 hA6
        hvS hwS hvWeight hwWeight hvw
        (fun x hx ↦ by
          rcases (hexhaust x).mp hx with h | h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)) hsumVW
    exact P03TripleGeometry.rankThree
      (p03_supports_disjoint_of_weight_add_eq_eight
        huWeight hvWeight huvWeight)
      (p03_supports_disjoint_of_weight_add_eq_eight
        huWeight hwWeight huwWeight)
      (p03_supports_disjoint_of_weight_add_eq_eight
        hvWeight hwWeight hvwWeight)

/-- Profile-shaped wrapper. The `A₁` and `A₃` hypotheses are retained to
match the p03 profile, although pair-sum parity makes them unnecessary here. -/
theorem p03_exists_classified_weightFour_triple
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (_hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (_hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hA6 : weightDistribution S 6 = 0) :
    ∃ u v w : Pauli 14,
      u ∈ S ∧ pauliWeight u = 4 ∧
      v ∈ S ∧ pauliWeight v = 4 ∧
      w ∈ S ∧ pauliWeight w = 4 ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
        x = u ∨ x = v ∨ x = w) ∧
      P03TripleGeometry u v w := by
  obtain ⟨u, v, w, huv, huw, hvw, hexhaust⟩ :=
    exists_three_of_weightDistribution_eq_three S hA4
  have hu : u ∈ S ∧ pauliWeight u = 4 :=
    (hexhaust u).mpr (Or.inl rfl)
  have hv : v ∈ S ∧ pauliWeight v = 4 :=
    (hexhaust v).mpr (Or.inr (Or.inl rfl))
  have hw : w ∈ S ∧ pauliWeight w = 4 :=
    (hexhaust w).mpr (Or.inr (Or.inr rfl))
  refine ⟨u, v, w, hu.1, hu.2, hv.1, hv.2, hw.1, hw.2,
    huv, huw, hvw, hexhaust, ?_⟩
  exact p03_classify_weightFour_triple S hiso hA2 hA6
    hu.1 hv.1 hw.1 hu.2 hv.2 hw.2 huv huw hvw hexhaust

end Quantum1435
