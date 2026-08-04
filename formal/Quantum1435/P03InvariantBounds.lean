import Quantum1435.P03CollisionAnalytic
import Quantum1435.P03SelectedSum
import Mathlib.Tactic

/-!
# Invariant collision bounds for the p03 branch

This file proves collision-degree bounds from coordinate-free support
hypotheses.  In particular, no explicit normal-form list is evaluated.

The load-bearing observation is that a collision between a weight-three word
and a weight-four translation uses exactly two coordinates in their support
intersection.  Therefore a weight-three word cannot collide with two
translations whose supports are disjoint.
-/

namespace Quantum1435

/-- The common support of two computational Pauli words, expressed using the
semantic support from `P03NormalForms`. -/
def p03CommonSupport (u v : CollisionWord) : Finset (Fin 14) :=
  p03Support (CollisionWord.toPauli u) ∩
    p03Support (CollisionWord.toPauli v)

private theorem card_filter_eq_sum_indicator
    (p : Fin 14 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ i, if p i then 1 else 0 := by
  simp

/-- The analytic overlap count is the cardinality of the common support. -/
theorem collisionOverlapCount_eq_card_commonSupport
    (word translation : CollisionWord) :
    collisionOverlapCount word translation =
      (p03CommonSupport word translation).card := by
  rw [show p03CommonSupport word translation =
      Finset.univ.filter (fun i => word i ≠ .I ∧ translation i ≠ .I) by
    ext i
    simp [p03CommonSupport, p03Support, CollisionWord.toPauli]]
  unfold collisionOverlapCount p03CategoryC p03CategoryD
    CollisionWord.toPauli
  rw [card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    card_filter_eq_sum_indicator, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases word i <;> cases translation i <;> decide

/-- The semantic support cardinality agrees with computational weight. -/
theorem card_p03Support_toPauli (word : CollisionWord) :
    (p03Support (CollisionWord.toPauli word)).card =
      CollisionWord.weight word := by
  unfold p03Support CollisionWord.toPauli CollisionWord.weight
  congr 1
  ext i
  simp

/-- A collision with a weight-four translation cuts out exactly two points of
the weight-three word's support. -/
theorem card_commonSupport_eq_two_of_isCollision
    {word translation : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (htranslation : CollisionWord.weight translation = 4)
    (hcollision : IsCollision word translation) :
    (p03CommonSupport word translation).card = 2 := by
  rw [← collisionOverlapCount_eq_card_commonSupport]
  exact (isCollision_iff_overlap_two_and_matching_two
    word translation hword htranslation).mp hcollision |>.1

/-- A weight-three word cannot collide with two weight-four translations
having disjoint supports. -/
theorem not_isCollision_pair_of_disjoint_support
    {word u v : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (hdisjoint : Disjoint (p03Support (CollisionWord.toPauli u))
      (p03Support (CollisionWord.toPauli v))) :
    ¬ (IsCollision word u ∧ IsCollision word v) := by
  rintro ⟨hcu, hcv⟩
  let su := p03CommonSupport word u
  let sv := p03CommonSupport word v
  have hsu : su.card = 2 :=
    card_commonSupport_eq_two_of_isCollision hword hu hcu
  have hsv : sv.card = 2 :=
    card_commonSupport_eq_two_of_isCollision hword hv hcv
  have hsdisjoint : Disjoint su sv := by
    rw [Finset.disjoint_left]
    intro i hiu hiv
    apply Finset.disjoint_left.mp hdisjoint
      (show i ∈ p03Support (CollisionWord.toPauli u) from
        (Finset.mem_inter.mp hiu).2)
      (show i ∈ p03Support (CollisionWord.toPauli v) from
        (Finset.mem_inter.mp hiv).2)
  have hunion_card : (su ∪ sv).card = 4 := by
    rw [Finset.card_union_of_disjoint hsdisjoint, hsu, hsv]
  have hunion_subset : su ∪ sv ⊆ p03Support (CollisionWord.toPauli word) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiu | hiv
    · exact (Finset.mem_inter.mp hiu).1
    · exact (Finset.mem_inter.mp hiv).1
  have hle := Finset.card_le_card hunion_subset
  rw [hunion_card, card_p03Support_toPauli, hword] at hle
  omega

/-- Any weight-three word has collision degree at most one against a list of
pairwise support-disjoint weight-four translations. -/
theorem collisionDegree_le_one_of_pairwise_disjoint_support
    {word : CollisionWord} {translations : List CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hweight : ∀ t ∈ translations, CollisionWord.weight t = 4)
    (hpairwise : translations.Pairwise fun u v =>
      Disjoint (p03Support (CollisionWord.toPauli u))
        (p03Support (CollisionWord.toPauli v))) :
    collisionDegree word translations ≤ 1 := by
  induction translations with
  | nil => simp [collisionDegree]
  | cons t ts ih =>
      rw [List.pairwise_cons] at hpairwise
      have ht : CollisionWord.weight t = 4 := hweight t (by simp)
      have hweight_ts : ∀ v ∈ ts, CollisionWord.weight v = 4 := by
        intro v hv
        exact hweight v (by simp [hv])
      by_cases hcollision : IsCollision word t
      · have hnone : ∀ v ∈ ts, ¬ IsCollision word v := by
          intro v hv hcv
          exact not_isCollision_pair_of_disjoint_support hword ht
            (hweight_ts v hv) (hpairwise.1 v hv) ⟨hcollision, hcv⟩
        have hfilter : ts.filter (fun v => IsCollision word v) = [] := by
          rw [List.filter_eq_nil_iff]
          intro v hv
          simp [hnone v hv]
        simp [collisionDegree, hcollision, hfilter]
      · simpa [collisionDegree, hcollision] using ih hweight_ts hpairwise.2

/-! ## The stronger shared-bin invariant

Support-disjointness is more than is needed.  Two collisions are already
incompatible when the translations never carry the same nonidentity label at
one coordinate.  This is exactly the invariant needed by the rank-two
category-`p = 0` case.
-/

/-- Coordinates on which two words carry the same nonidentity Pauli label. -/
def p03MatchingSupport (u v : CollisionWord) : Finset (Fin 14) :=
  Finset.univ.filter fun i => u i ≠ .I ∧ u i = v i

/-- Two translations share no Pauli bin. -/
def P03NoSharedBin (u v : CollisionWord) : Prop :=
  p03MatchingSupport u v = ∅

private theorem localPauli_bits_matching_iff (a b : LocalPauli) :
    a.toBits ≠ 0 ∧ a.toBits = b.toBits ↔ a ≠ .I ∧ a = b := by
  cases a <;> cases b <;> decide

private theorem localPauli_matching_self_add_iff (a b : LocalPauli) :
    a ≠ .I ∧ a = LocalPauli.add a b ↔
      a.toBits ≠ 0 ∧ b.toBits = 0 := by
  cases a <;> cases b <;> decide

private theorem localPauli_matching_right_add_iff (a b : LocalPauli) :
    b ≠ .I ∧ b = LocalPauli.add a b ↔
      a.toBits = 0 ∧ b.toBits ≠ 0 := by
  cases a <;> cases b <;> decide

/-- The analytic matching count is the cardinality of the matching support. -/
theorem collisionMatchingCount_eq_card_matchingSupport
    (word translation : CollisionWord) :
    collisionMatchingCount word translation =
      (p03MatchingSupport word translation).card := by
  unfold collisionMatchingCount p03CategoryC p03MatchingSupport
    CollisionWord.toPauli
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact localPauli_bits_matching_iff (word i) (translation i)

/-- A weight-three word cannot collide with two weight-four translations
which share no equal nonidentity Pauli bin. -/
theorem not_isCollision_pair_of_noSharedBin
    {word u v : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (hno : P03NoSharedBin u v) :
    ¬ (IsCollision word u ∧ IsCollision word v) := by
  rintro ⟨hcu, hcv⟩
  let mu := p03MatchingSupport word u
  let mv := p03MatchingSupport word v
  have hmu : mu.card = 2 := by
    rw [← collisionMatchingCount_eq_card_matchingSupport]
    exact (isCollision_iff_overlap_two_and_matching_two
      word u hword hu).mp hcu |>.2
  have hmv : mv.card = 2 := by
    rw [← collisionMatchingCount_eq_card_matchingSupport]
    exact (isCollision_iff_overlap_two_and_matching_two
      word v hword hv).mp hcv |>.2
  have hdisjoint : Disjoint mu mv := by
    rw [Finset.disjoint_left]
    intro i hiu hiv
    have hiu' := Finset.mem_filter.mp hiu
    have hiv' := Finset.mem_filter.mp hiv
    have himatch : i ∈ p03MatchingSupport u v := by
      change i ∈ Finset.univ.filter (fun q => u q ≠ .I ∧ u q = v q)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      constructor
      · simpa [hiu'.2.2] using hiu'.2.1
      · exact hiu'.2.2.symm.trans hiv'.2.2
    rw [hno] at himatch
    exact Finset.notMem_empty i himatch
  have hunion_card : (mu ∪ mv).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hmu, hmv]
  have hunion_subset : mu ∪ mv ⊆ p03Support (CollisionWord.toPauli word) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiu | hiv
    · have hiu' := (Finset.mem_filter.mp hiu).2.1
      simpa [p03Support, CollisionWord.toPauli] using hiu'
    · have hiv' := (Finset.mem_filter.mp hiv).2.1
      simpa [p03Support, CollisionWord.toPauli] using hiv'
  have hle := Finset.card_le_card hunion_subset
  rw [hunion_card, card_p03Support_toPauli, hword] at hle
  omega

/-- Pairwise absence of shared Pauli bins bounds collision degree by one. -/
theorem collisionDegree_le_one_of_pairwise_noSharedBin
    {word : CollisionWord} {translations : List CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hweight : ∀ t ∈ translations, CollisionWord.weight t = 4)
    (hpairwise : translations.Pairwise P03NoSharedBin) :
    collisionDegree word translations ≤ 1 := by
  induction translations with
  | nil => simp [collisionDegree]
  | cons t ts ih =>
      rw [List.pairwise_cons] at hpairwise
      have ht : CollisionWord.weight t = 4 := hweight t (by simp)
      have hweight_ts : ∀ v ∈ ts, CollisionWord.weight v = 4 := by
        intro v hv
        exact hweight v (by simp [hv])
      by_cases hcollision : IsCollision word t
      · have hnone : ∀ v ∈ ts, ¬ IsCollision word v := by
          intro v hv hcv
          exact not_isCollision_pair_of_noSharedBin hword ht
            (hweight_ts v hv) (hpairwise.1 v hv) ⟨hcollision, hcv⟩
        have hfilter : ts.filter (fun v => IsCollision word v) = [] := by
          rw [List.filter_eq_nil_iff]
          intro v hv
          simp [hnone v hv]
        simp [collisionDegree, hcollision, hfilter]
      · simpa [collisionDegree, hcollision] using ih hweight_ts hpairwise.2

/-- Category `C = 0` says exactly that two translations share no Pauli bin. -/
theorem noSharedBin_of_categoryC_eq_zero {u v : CollisionWord}
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0) :
    P03NoSharedBin u v := by
  apply Finset.card_eq_zero.mp
  rw [← collisionMatchingCount_eq_card_matchingSupport]
  exact hC

/-- Matching bins of `u` and `u+v` are precisely category `A` for `(u,v)`. -/
theorem card_matchingSupport_self_add (u v : CollisionWord) :
    (p03MatchingSupport u (CollisionWord.add u v)).card =
      p03CategoryA (CollisionWord.toPauli u) (CollisionWord.toPauli v) := by
  unfold p03MatchingSupport p03CategoryA CollisionWord.toPauli
    CollisionWord.add
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact localPauli_matching_self_add_iff (u i) (v i)

/-- Matching bins of `v` and `u+v` are precisely category `B` for `(u,v)`. -/
theorem card_matchingSupport_right_add (u v : CollisionWord) :
    (p03MatchingSupport v (CollisionWord.add u v)).card =
      p03CategoryB (CollisionWord.toPauli u) (CollisionWord.toPauli v) := by
  unfold p03MatchingSupport p03CategoryB CollisionWord.toPauli
    CollisionWord.add
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact localPauli_matching_right_add_iff (u i) (v i)

/-- In the rank-two category pattern `p = 0`, every weight-three word has
collision degree at most one against the three nonzero plane elements. -/
theorem rankTwo_p0_collisionDegree_le_one
    {word u v : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0) :
    collisionDegree word [u, v, CollisionWord.add u v] ≤ 1 := by
  apply collisionDegree_le_one_of_pairwise_noSharedBin hword
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact huv
  · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact noSharedBin_of_categoryC_eq_zero hC
      · apply Finset.card_eq_zero.mp
        rw [card_matchingSupport_self_add, hA]
    · refine List.pairwise_cons.mpr ⟨?_, by simp⟩
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      subst t
      apply Finset.card_eq_zero.mp
      rw [card_matchingSupport_right_add, hB]

/-! ## End-to-end selected-set and edge bounds -/

/-- Pointwise degree at most one bounds the degree sum by the size of the
selected set. -/
theorem selected_degree_sum_le_card_of_pointwise_le_one
    {translations : List CollisionWord} (selected : Finset CollisionWord)
    (hdegree : ∀ word ∈ selected, collisionDegree word translations ≤ 1) :
    (∑ word ∈ selected, collisionDegree word translations) ≤ selected.card := by
  calc
    (∑ word ∈ selected, collisionDegree word translations) ≤
        ∑ _word ∈ selected, 1 := Finset.sum_le_sum hdegree
    _ = selected.card := by simp

/-- Pairwise support-disjoint translations give the p03 selected-set degree
sum bound `24` without a concrete normal-form computation. -/
theorem selected_degree_sum_le_twenty_four_of_pairwise_disjoint_support
    {translations : List CollisionWord} (selected : Finset CollisionWord)
    (hselected : selected.card ≤ 24)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (htranslation : ∀ t ∈ translations, CollisionWord.weight t = 4)
    (hpairwise : translations.Pairwise fun u v =>
      Disjoint (p03Support (CollisionWord.toPauli u))
        (p03Support (CollisionWord.toPauli v))) :
    (∑ word ∈ selected, collisionDegree word translations) ≤ 24 := by
  exact (selected_degree_sum_le_card_of_pointwise_le_one selected fun word hmem =>
    collisionDegree_le_one_of_pairwise_disjoint_support
      (hword word hmem) htranslation hpairwise).trans hselected

/-- With the handshake inequality, the support-disjoint branch has at most
`12` collision edges. -/
theorem edges_le_twelve_of_pairwise_disjoint_support
    {translations : List CollisionWord} (selected : Finset CollisionWord)
    (hselected : selected.card ≤ 24)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (htranslation : ∀ t ∈ translations, CollisionWord.weight t = 4)
    (hpairwise : translations.Pairwise fun u v =>
      Disjoint (p03Support (CollisionWord.toPauli u))
        (p03Support (CollisionWord.toPauli v)))
    (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ word ∈ selected, collisionDegree word translations) :
    edges ≤ 12 := by
  simpa using edges_le_of_selected_degree_sum
    (fun word => collisionDegree word translations) selected 24 edges
    (selected_degree_sum_le_twenty_four_of_pairwise_disjoint_support selected
      hselected hword htranslation hpairwise) handshake

/-- The invariant rank-two category-`p = 0` branch has selected degree sum at
most `24`. -/
theorem rankTwo_p0_selected_degree_sum_le_twenty_four
    {u v : CollisionWord} (selected : Finset CollisionWord)
    (hselected : selected.card ≤ 24)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0) :
    (∑ word ∈ selected,
      collisionDegree word [u, v, CollisionWord.add u v]) ≤ 24 := by
  exact (selected_degree_sum_le_card_of_pointwise_le_one selected fun word hmem =>
    rankTwo_p0_collisionDegree_le_one (hword word hmem)
      hu hv huv hA hB hC).trans hselected

/-- With the handshake inequality, the invariant rank-two category-`p = 0`
branch has at most `12` collision edges. -/
theorem rankTwo_p0_edges_le_twelve
    {u v : CollisionWord} (selected : Finset CollisionWord)
    (hselected : selected.card ≤ 24)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0)
    (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ word ∈ selected,
        collisionDegree word [u, v, CollisionWord.add u v]) :
    edges ≤ 12 := by
  simpa using edges_le_of_selected_degree_sum
    (fun word => collisionDegree word [u, v, CollisionWord.add u v])
    selected 24 edges
    (rankTwo_p0_selected_degree_sum_le_twenty_four selected hselected hword
      hu hv huv hA hB hC) handshake

end Quantum1435
