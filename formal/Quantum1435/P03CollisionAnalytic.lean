import Quantum1435.P03CollisionChecker
import Quantum1435.P03NormalForms

namespace Quantum1435

@[simp] theorem LocalPauli.add_eq_left_iff (a b : LocalPauli) :
    LocalPauli.add a b = a ↔ b = .I := by
  cases a <;> cases b <;> decide

@[simp] theorem LocalPauli.left_eq_add_iff (a b : LocalPauli) :
    a = LocalPauli.add a b ↔ b = .I := by
  cases a <;> cases b <;> decide

/-- Number of positions where both words are nonidentity. -/
def collisionOverlapCount (word translation : CollisionWord) : ℕ :=
  p03CategoryC (CollisionWord.toPauli word) (CollisionWord.toPauli translation) +
    p03CategoryD (CollisionWord.toPauli word) (CollisionWord.toPauli translation)

/-- Number of positions where the two words have the same nonidentity label. -/
def collisionMatchingCount (word translation : CollisionWord) : ℕ :=
  p03CategoryC (CollisionWord.toPauli word) (CollisionWord.toPauli translation)

/-- Sharing a bin with `word + translation` is exactly having a nonidentity
coordinate of `word` outside the support of `translation`. -/
theorem sharesBin_add_iff_exists_outside (word translation : CollisionWord) :
    sharesBin word (CollisionWord.add word translation) = true ↔
      ∃ i : Fin 14, word i ≠ .I ∧ translation i = .I := by
  unfold sharesBin
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hb, htrue⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    simp only [id_eq] at htrue
    have hi : word i ≠ .I ∧
        word i = CollisionWord.add word translation i :=
      of_decide_eq_true htrue
    exact ⟨i, hi.1, (LocalPauli.left_eq_add_iff _ _).mp hi.2⟩
  · rintro ⟨i, hiw, hit⟩
    refine ⟨true, ?_, rfl⟩
    rw [List.mem_ofFn]
    refine ⟨i, ?_⟩
    simp [CollisionWord.add, hiw, hit]

/-- The shared-bin condition is positivity of category A. -/
theorem sharesBin_add_iff_categoryA_pos (word translation : CollisionWord) :
    sharesBin word (CollisionWord.add word translation) = true ↔
      0 < p03CategoryA (CollisionWord.toPauli word)
        (CollisionWord.toPauli translation) := by
  rw [sharesBin_add_iff_exists_outside]
  unfold p03CategoryA
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hiw, hit⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩⟩
    simpa [CollisionWord.toPauli] using And.intro hiw hit
  · rintro ⟨i, hi⟩
    have hi' := (Finset.mem_filter.mp hi).2
    exact ⟨i, by simpa [CollisionWord.toPauli] using hi'⟩

/-- For weight-three and weight-four words, the finite collision predicate is
exactly two support overlaps, both carrying matching labels. -/
theorem isCollision_iff_overlap_two_and_matching_two
    (word translation : CollisionWord)
    (hword : CollisionWord.weight word = 3)
    (htranslation : CollisionWord.weight translation = 4) :
    IsCollision word translation ↔
      collisionOverlapCount word translation = 2 ∧
        collisionMatchingCount word translation = 2 := by
  let u := CollisionWord.toPauli word
  let v := CollisionWord.toPauli translation
  have hu : pauliWeight u = 3 := by
    rw [← CollisionWord.weight_eq_pauliWeight]
    exact hword
  have hv : pauliWeight v = 4 := by
    rw [← CollisionWord.weight_eq_pauliWeight]
    exact htranslation
  have hU := pauliWeight_eq_categories_ACD u v
  have hV := pauliWeight_eq_categories_BCD u v
  have hUV := pauliWeight_add_eq_categories_ABD u v
  rw [hu] at hU
  rw [hv] at hV
  rw [isCollision_iff_pauli]
  change pauliWeight (u + v) = 3 ∧
      sharesBin word (CollisionWord.add word translation) = true ↔ _
  rw [sharesBin_add_iff_categoryA_pos]
  change pauliWeight (u + v) = 3 ∧ 0 < p03CategoryA u v ↔ _
  rw [collisionOverlapCount, collisionMatchingCount]
  change _ ↔ p03CategoryC u v + p03CategoryD u v = 2 ∧
    p03CategoryC u v = 2
  constructor
  · rintro ⟨hsum, hA⟩
    rw [hsum] at hUV
    constructor <;> omega
  · rintro ⟨hoverlap, hmatch⟩
    constructor <;> omega

/-! ## Generic degree facts for three translations -/

/-- Collision degree against a triple is the sum of its three indicator
functions.  No distinctness assumption on the translations is needed. -/
theorem collisionDegree_triple_eq_indicator_sum
    (word a b c : CollisionWord) :
    collisionDegree word [a, b, c] =
      (if IsCollision word a then 1 else 0) +
      (if IsCollision word b then 1 else 0) +
      (if IsCollision word c then 1 else 0) := by
  by_cases ha : IsCollision word a <;>
    by_cases hb : IsCollision word b <;>
    by_cases hc : IsCollision word c <;>
    simp [collisionDegree, List.filter, ha, hb, hc]

/-- A word collides with at most three members of a translation triple. -/
theorem collisionDegree_triple_le_three (word a b c : CollisionWord) :
    collisionDegree word [a, b, c] ≤ 3 := by
  by_cases ha : IsCollision word a <;>
    by_cases hb : IsCollision word b <;>
    by_cases hc : IsCollision word c <;>
    simp [collisionDegree, List.filter, ha, hb, hc]

/-- Degree greater than two against a translation triple means collision with
all three translations. -/
theorem two_lt_collisionDegree_triple_iff (word a b c : CollisionWord) :
    2 < collisionDegree word [a, b, c] ↔
      IsCollision word a ∧ IsCollision word b ∧ IsCollision word c := by
  by_cases ha : IsCollision word a <;>
    by_cases hb : IsCollision word b <;>
    by_cases hc : IsCollision word c <;>
    simp [collisionDegree, List.filter, ha, hb, hc]

end Quantum1435
