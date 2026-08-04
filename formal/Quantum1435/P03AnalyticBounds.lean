import Quantum1435.P03CollisionAnalytic
import Mathlib.Tactic

/-!
# Analytic degree bounds for the p03 normal forms

This module replaces the large concrete p03 reduction with small structural
arguments for the four displayed normal forms.  It builds on the semantic
collision reduction in `P03CollisionAnalytic`.
-/

namespace Quantum1435

open scoped BigOperators

private theorem card_filter_eq_sum_indicator
    (p : Fin 14 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ i, if p i then 1 else 0 := by
  simp

/-- The category-based overlap count is the direct support-intersection
cardinality. -/
theorem collisionOverlapCount_eq_card_filter (word translation : CollisionWord) :
    collisionOverlapCount word translation =
      (Finset.univ.filter fun i => word i ≠ .I ∧ translation i ≠ .I).card := by
  unfold collisionOverlapCount p03CategoryC p03CategoryD
  rw [card_filter_eq_sum_indicator, card_filter_eq_sum_indicator,
    card_filter_eq_sum_indicator, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hword : word i <;> cases htranslation : translation i <;>
    simp [CollisionWord.toPauli, LocalPauli.toBits, hword, htranslation]

/-- The category-based matching count is the direct equal-label support
cardinality. -/
theorem collisionMatchingCount_eq_card_filter (word translation : CollisionWord) :
    collisionMatchingCount word translation =
      (Finset.univ.filter fun i => word i ≠ .I ∧ word i = translation i).card := by
  unfold collisionMatchingCount p03CategoryC
  apply congrArg Finset.card
  ext i
  cases hword : word i <;> cases htranslation : translation i <;>
    simp [CollisionWord.toPauli, LocalPauli.toBits, hword, htranslation]

/-! ## Sparse form for canonical weight-three words -/

@[simp] theorem nonzeroLabel_ne_I (a : Fin 3) : nonzeroLabel a ≠ .I := by
  fin_cases a <;> decide

theorem canonicalWeightThreeWord_ne_I_iff
    (i j k : Fin 14) (a b c : Fin 3) (q : Fin 14) :
    canonicalWeightThreeWord i j k a b c q ≠ .I ↔
      q = i ∨ q = j ∨ q = k := by
  unfold canonicalWeightThreeWord
  split_ifs <;> simp_all

theorem canonicalWeightThreeWord_weight
    {i j k : Fin 14} (a b c : Fin 3) (hij : i < j) (hjk : j < k) :
    CollisionWord.weight (canonicalWeightThreeWord i j k a b c) = 3 := by
  unfold CollisionWord.weight
  rw [show (Finset.univ.filter fun q =>
      canonicalWeightThreeWord i j k a b c q ≠ .I) = {i, j, k} by
    ext q
    simp [canonicalWeightThreeWord_ne_I_iff]]
  have hik : i ≠ k := ne_of_lt (hij.trans hjk)
  have hij' : i ≠ j := ne_of_lt hij
  have hjk' : j ≠ k := ne_of_lt hjk
  simp [hij', hik, hjk']

/-- Overlap count obtained by looking only at the three nonzero coordinates
of a canonical word. -/
def sparseOverlap (translation : CollisionWord) (i j k : Fin 14) : ℕ :=
  (if translation i ≠ .I then 1 else 0) +
    (if translation j ≠ .I then 1 else 0) +
      (if translation k ≠ .I then 1 else 0)

/-- Matching-label count obtained from the same three coordinates. -/
def sparseMatches (translation : CollisionWord) (i j k : Fin 14)
    (a b c : Fin 3) : ℕ :=
  (if nonzeroLabel a = translation i then 1 else 0) +
    (if nonzeroLabel b = translation j then 1 else 0) +
      (if nonzeroLabel c = translation k then 1 else 0)

theorem collisionOverlap_canonical
    {i j k : Fin 14} (a b c : Fin 3) (translation : CollisionWord)
    (hij : i < j) (hjk : j < k) :
    collisionOverlapCount (canonicalWeightThreeWord i j k a b c) translation =
      sparseOverlap translation i j k := by
  rw [collisionOverlapCount_eq_card_filter]
  rw [show (Finset.univ.filter fun q =>
      canonicalWeightThreeWord i j k a b c q ≠ .I ∧ translation q ≠ .I) =
      ({i, j, k} : Finset (Fin 14)).filter (fun q => translation q ≠ .I) by
    ext q
    simp [canonicalWeightThreeWord_ne_I_iff]]
  have hik : i ≠ k := ne_of_lt (hij.trans hjk)
  have hij' : i ≠ j := ne_of_lt hij
  have hjk' : j ≠ k := ne_of_lt hjk
  by_cases hi : translation i ≠ .I <;>
    by_cases hj : translation j ≠ .I <;>
      by_cases hk : translation k ≠ .I
  all_goals
    simp [Finset.filter_insert, Finset.filter_singleton, sparseOverlap,
      hij', hik, hjk', hi, hj, hk]

theorem collisionMatches_canonical
    {i j k : Fin 14} {a b c : Fin 3} (translation : CollisionWord)
    (hij : i < j) (hjk : j < k) :
    collisionMatchingCount (canonicalWeightThreeWord i j k a b c) translation =
      sparseMatches translation i j k a b c := by
  rw [collisionMatchingCount_eq_card_filter]
  rw [show (Finset.univ.filter fun q =>
      canonicalWeightThreeWord i j k a b c q ≠ .I ∧
        canonicalWeightThreeWord i j k a b c q = translation q) =
      ({i, j, k} : Finset (Fin 14)).filter (fun q =>
        canonicalWeightThreeWord i j k a b c q = translation q) by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [canonicalWeightThreeWord_ne_I_iff]]
  have hik : i ≠ k := ne_of_lt (hij.trans hjk)
  have hij' : i ≠ j := ne_of_lt hij
  have hji : j ≠ i := hij'.symm
  have hjk' : j ≠ k := ne_of_lt hjk
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk'.symm
  by_cases hi : nonzeroLabel a = translation i <;>
    by_cases hj : nonzeroLabel b = translation j <;>
      by_cases hk : nonzeroLabel c = translation k
  all_goals
    simp [Finset.filter_insert, Finset.filter_singleton, sparseMatches,
      canonicalWeightThreeWord, hij', hji, hik, hki, hjk', hkj, hi, hj, hk]

/-- Sparse collision characterization for sorted canonical coordinates. -/
theorem isCollision_canonical_iff
    {i j k : Fin 14} {a b c : Fin 3} {translation : CollisionWord}
    (hij : i < j) (hjk : j < k)
    (htranslation : CollisionWord.weight translation = 4) :
    IsCollision (canonicalWeightThreeWord i j k a b c) translation ↔
      sparseOverlap translation i j k = 2 ∧
        sparseMatches translation i j k a b c = 2 := by
  rw [isCollision_iff_overlap_two_and_matching_two _ _
    (canonicalWeightThreeWord_weight a b c hij hjk) htranslation,
    collisionOverlap_canonical a b c translation hij hjk,
    collisionMatches_canonical translation hij hjk]

/-! ## Sparse degree interface -/

/-- The sparse predicate whose equivalence to `IsCollision` was proved above. -/
def sparseCollisionTest (translation : CollisionWord) (i j k : Fin 14)
    (a b c : Fin 3) : Bool :=
  decide (sparseOverlap translation i j k = 2 ∧
    sparseMatches translation i j k a b c = 2)

/-- Degree computed from only the three occupied coordinates. -/
def sparseCollisionDegree (translations : List CollisionWord) (i j k : Fin 14)
    (a b c : Fin 3) : ℕ :=
  (translations.filter fun translation =>
    sparseCollisionTest translation i j k a b c).length

end Quantum1435
