import Quantum1435.P03RankTwo2Check
import Quantum1435.P03SelectedSum

/-!
# Semantic threshold bounds for the p03 normal forms

The resource-heavy checks in the four `P03*Check` modules use the sparse
three-coordinate representation.  This module connects those checked facts
back to `p03CollisionScore`, whose input is the canonical
`WeightThreeParameter` used by the semantic collision development.

No enumeration of the 9,828-element parameter type occurs here.  The p1
exceptional set is proved subsingleton from its exact coordinate
characterization.  The p2 exceptional set is injected into the explicit
`2 × 2 × 2` set of possible supports.  The resulting bounds feed the generic
selected-set theorem to give the manuscript's top-24 degree sums and the
corresponding conditional handshake edge bounds.
-/

namespace Quantum1435

open scoped BigOperators

/-! ## From sparse tests to semantic collision degree -/

/-- Every member of an explicit normal-form generator list has weight four.
This extracts the semantic fact from the already checked well-formedness
theorem rather than re-evaluating the words in this module. -/
private theorem normalFormGenerator_weight_four
    (form : P03NormalForm) (translation : CollisionWord)
    (htranslation : translation ∈ p03NormalFormGenerators form) :
    CollisionWord.weight translation = 4 := by
  have hall := (p03NormalFormGenerators_wellFormed form).2.1
  have hchecked := (List.all_eq_true.mp hall) translation htranslation
  exact of_decide_eq_true hchecked

/-- On a sorted sparse support, filtering by the semantic collision predicate
and filtering by the sparse Boolean predicate produce the same degree. -/
private theorem collisionDegree_canonical_eq_sparse
    {i j k : Fin 14} {a b c : Fin 3}
    (translations : List CollisionWord)
    (hij : i < j) (hjk : j < k)
    (hweight : ∀ translation ∈ translations,
      CollisionWord.weight translation = 4) :
    collisionDegree (canonicalWeightThreeWord i j k a b c) translations =
      sparseCollisionDegree translations i j k a b c := by
  unfold collisionDegree sparseCollisionDegree
  apply congrArg List.length
  apply List.filter_congr
  intro translation htranslation
  unfold sparseCollisionTest
  exact Bool.decide_congr
    (isCollision_canonical_iff hij hjk
      (hweight translation htranslation))

/-- The semantic score of a canonical parameter is its sparse degree. -/
theorem p03CollisionScore_eq_sparse (form : P03NormalForm)
    (p : WeightThreeParameter) :
    p03CollisionScore form p =
      sparseCollisionDegree (p03NormalFormGenerators form)
        p.1.support.first p.1.support.second p.1.support.third
        p.1.labels.first p.1.labels.second p.1.labels.third := by
  unfold p03CollisionScore
  change collisionDegree
      (canonicalWeightThreeWord
        p.1.support.first p.1.support.second p.1.support.third
        p.1.labels.first p.1.labels.second p.1.labels.third)
      (p03NormalFormGenerators form) = _
  exact collisionDegree_canonical_eq_sparse
    (p03NormalFormGenerators form) p.2.1 p.2.2
    (normalFormGenerator_weight_four form)

/-! ## Checked pointwise bounds and exceptional characterizations -/

theorem rankThree_collisionScore_le_one (p : WeightThreeParameter) :
    p03CollisionScore .rankThree p ≤ 1 := by
  rw [p03CollisionScore_eq_sparse]
  exact rankThree_sparse_degree_le_one
    p.1.support.first p.1.support.second p.1.support.third
    p.1.labels.first p.1.labels.second p.1.labels.third p.2

theorem rankTwo0_collisionScore_le_one (p : WeightThreeParameter) :
    p03CollisionScore .rankTwo0 p ≤ 1 := by
  rw [p03CollisionScore_eq_sparse]
  exact rankTwo0_sparse_degree_le_one
    p.1.support.first p.1.support.second p.1.support.third
    p.1.labels.first p.1.labels.second p.1.labels.third p.2

/-- A collision degree against any of the explicit triples is at most three. -/
private theorem rankTwo1_collisionScore_le_three (p : WeightThreeParameter) :
    p03CollisionScore .rankTwo1 p ≤ 3 := by
  change collisionDegree p.word rankTwo1Generators ≤ 3
  unfold rankTwo1Generators
  apply collisionDegree_triple_le_three

private theorem rankTwo2_collisionScore_le_three (p : WeightThreeParameter) :
    p03CollisionScore .rankTwo2 p ≤ 3 := by
  change collisionDegree p.word rankTwo2Generators ≤ 3
  unfold rankTwo2Generators
  apply collisionDegree_triple_le_three

/-- The p1 exceptional semantic word is exactly the all-X word on
coordinates `0,1,2`. -/
theorem rankTwo1_collisionScore_high_iff (p : WeightThreeParameter) :
    1 < p03CollisionScore .rankTwo1 p ↔
      p.1.support.first = 0 ∧ p.1.support.second = 1 ∧
        p.1.support.third = 2 ∧ p.1.labels.first = 0 ∧
        p.1.labels.second = 0 ∧ p.1.labels.third = 0 := by
  rw [p03CollisionScore_eq_sparse]
  simpa [p03NormalFormGenerators] using
    (rankTwo1_sparse_high_iff
      p.1.support.first p.1.support.second p.1.support.third
      p.1.labels.first p.1.labels.second p.1.labels.third p.2)

/-- The p2 degree-three semantic words have one all-X coordinate in each of
the pairs `{0,1}`, `{2,3}`, and `{4,5}`. -/
theorem rankTwo2_collisionScore_high_iff (p : WeightThreeParameter) :
    2 < p03CollisionScore .rankTwo2 p ↔
      (p.1.support.first = 0 ∨ p.1.support.first = 1) ∧
        (p.1.support.second = 2 ∨ p.1.support.second = 3) ∧
        (p.1.support.third = 4 ∨ p.1.support.third = 5) ∧
        p.1.labels.first = 0 ∧ p.1.labels.second = 0 ∧
        p.1.labels.third = 0 := by
  rw [p03CollisionScore_eq_sparse]
  simpa [p03NormalFormGenerators] using
    (rankTwo2_sparse_high_iff
      p.1.support.first p.1.support.second p.1.support.third
      p.1.labels.first p.1.labels.second p.1.labels.third p.2)

/-! ## Small exceptional sets -/

/-- Equality of the six data fields determines a canonical parameter; the
proof of sortedness is irrelevant. -/
private theorem weightThreeParameter_eq_of_fields
    (p q : WeightThreeParameter)
    (hfirst : p.1.support.first = q.1.support.first)
    (hsecond : p.1.support.second = q.1.support.second)
    (hthird : p.1.support.third = q.1.support.third)
    (hlabelFirst : p.1.labels.first = q.1.labels.first)
    (hlabelSecond : p.1.labels.second = q.1.labels.second)
    (hlabelThird : p.1.labels.third = q.1.labels.third) : p = q := by
  apply Subtype.ext
  rcases p with ⟨⟨⟨pi, pj, pk⟩, ⟨pa, pb, pc⟩⟩, hp⟩
  rcases q with ⟨⟨⟨qi, qj, qk⟩, ⟨qa, qb, qc⟩⟩, hq⟩
  dsimp at hfirst hsecond hthird hlabelFirst hlabelSecond hlabelThird
  subst qi
  subst qj
  subst qk
  subst qa
  subst qb
  subst qc
  rfl

/-- Every selected p1 exceptional set is a singleton or empty. -/
theorem rankTwo1_selected_exception_card_le_one
    (selected : Finset WeightThreeParameter) :
    (selected.filter fun p =>
      1 < p03CollisionScore .rankTwo1 p).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  have hpHigh := (rankTwo1_collisionScore_high_iff p).mp
    (Finset.mem_filter.mp hp).2
  have hqHigh := (rankTwo1_collisionScore_high_iff q).mp
    (Finset.mem_filter.mp hq).2
  rcases hpHigh with ⟨hpi, hpj, hpk, hpa, hpb, hpc⟩
  rcases hqHigh with ⟨hqi, hqj, hqk, hqa, hqb, hqc⟩
  exact weightThreeParameter_eq_of_fields p q
    (hpi.trans hqi.symm) (hpj.trans hqj.symm) (hpk.trans hqk.symm)
    (hpa.trans hqa.symm) (hpb.trans hqb.symm) (hpc.trans hqc.symm)

/-- The support coordinates retained for the p2 exceptional-set injection. -/
private def weightThreeSupportKey (p : WeightThreeParameter) :
    (Fin 14 × Fin 14) × Fin 14 :=
  ((p.1.support.first, p.1.support.second), p.1.support.third)

private def p2FirstCoordinates : Finset (Fin 14) := {0, 1}
private def p2SecondCoordinates : Finset (Fin 14) := {2, 3}
private def p2ThirdCoordinates : Finset (Fin 14) := {4, 5}

/-- The eight possible supports of a p2 degree-three word. -/
private def p2ExceptionalSupports : Finset ((Fin 14 × Fin 14) × Fin 14) :=
  (p2FirstCoordinates.product p2SecondCoordinates).product p2ThirdCoordinates

private theorem p2ExceptionalSupports_card : p2ExceptionalSupports.card = 8 := by
  decide

/-- Every selected p2 exceptional set injects into its `2 × 2 × 2` possible
supports.  The labels need not be included in the key because the checked
characterization forces all three of them to be X. -/
theorem rankTwo2_selected_exception_card_le_eight
    (selected : Finset WeightThreeParameter) :
    (selected.filter fun p =>
      2 < p03CollisionScore .rankTwo2 p).card ≤ 8 := by
  let exceptional := selected.filter fun p =>
    2 < p03CollisionScore .rankTwo2 p
  have hinjective : Set.InjOn weightThreeSupportKey exceptional := by
    intro p hp q hq hkey
    have hpHigh := (rankTwo2_collisionScore_high_iff p).mp
      (Finset.mem_filter.mp hp).2
    have hqHigh := (rankTwo2_collisionScore_high_iff q).mp
      (Finset.mem_filter.mp hq).2
    rcases hpHigh with ⟨_, _, _, hpa, hpb, hpc⟩
    rcases hqHigh with ⟨_, _, _, hqa, hqb, hqc⟩
    exact weightThreeParameter_eq_of_fields p q
      (congrArg (fun support => support.1.1) hkey)
      (congrArg (fun support => support.1.2) hkey)
      (congrArg (fun support => support.2) hkey)
      (hpa.trans hqa.symm) (hpb.trans hqb.symm) (hpc.trans hqc.symm)
  have hsubset : exceptional.image weightThreeSupportKey ⊆
      p2ExceptionalSupports := by
    intro support hsupport
    rcases Finset.mem_image.mp hsupport with ⟨p, hp, rfl⟩
    have hpHigh := (rankTwo2_collisionScore_high_iff p).mp
      (Finset.mem_filter.mp hp).2
    rcases hpHigh with ⟨hfirst, hsecond, hthird, _, _, _⟩
    simpa [weightThreeSupportKey, p2ExceptionalSupports,
      p2FirstCoordinates, p2SecondCoordinates, p2ThirdCoordinates] using
      And.intro (And.intro hfirst hsecond) hthird
  calc
    (selected.filter fun p =>
        2 < p03CollisionScore .rankTwo2 p).card = exceptional.card := rfl
    _ = (exceptional.image weightThreeSupportKey).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ p2ExceptionalSupports.card := Finset.card_le_card hsubset
    _ = 8 := p2ExceptionalSupports_card

/-! ## Top-24 degree sums -/

private theorem rankThree_selected_exception_card_zero
    (selected : Finset WeightThreeParameter) :
    (selected.filter fun p =>
      1 < p03CollisionScore .rankThree p).card ≤ 0 := by
  rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  exact Nat.not_lt_of_ge (rankThree_collisionScore_le_one p)

private theorem rankTwo0_selected_exception_card_zero
    (selected : Finset WeightThreeParameter) :
    (selected.filter fun p =>
      1 < p03CollisionScore .rankTwo0 p).card ≤ 0 := by
  rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  exact Nat.not_lt_of_ge (rankTwo0_collisionScore_le_one p)

theorem rankThree_selected_sum_le_24
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24) :
    (∑ p ∈ selected, p03CollisionScore .rankThree p) ≤ 24 := by
  simpa using sum_le_of_selected_threshold
    (fun p : WeightThreeParameter => p03CollisionScore .rankThree p)
    1 1 0 24 (by decide) selected hselected
    (fun p _ => rankThree_collisionScore_le_one p)
    (rankThree_selected_exception_card_zero selected)

theorem rankTwo0_selected_sum_le_24
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24) :
    (∑ p ∈ selected, p03CollisionScore .rankTwo0 p) ≤ 24 := by
  simpa using sum_le_of_selected_threshold
    (fun p : WeightThreeParameter => p03CollisionScore .rankTwo0 p)
    1 1 0 24 (by decide) selected hselected
    (fun p _ => rankTwo0_collisionScore_le_one p)
    (rankTwo0_selected_exception_card_zero selected)

theorem rankTwo1_selected_sum_le_26
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24) :
    (∑ p ∈ selected, p03CollisionScore .rankTwo1 p) ≤ 26 := by
  simpa using sum_le_of_selected_threshold
    (fun p : WeightThreeParameter => p03CollisionScore .rankTwo1 p)
    1 3 1 24 (by decide) selected hselected
    (fun p _ => rankTwo1_collisionScore_le_three p)
    (rankTwo1_selected_exception_card_le_one selected)

theorem rankTwo2_selected_sum_le_56
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24) :
    (∑ p ∈ selected, p03CollisionScore .rankTwo2 p) ≤ 56 := by
  simpa using sum_le_of_selected_threshold
    (fun p : WeightThreeParameter => p03CollisionScore .rankTwo2 p)
    2 3 8 24 (by decide) selected hselected
    (fun p _ => rankTwo2_collisionScore_le_three p)
    (rankTwo2_selected_exception_card_le_eight selected)

/-! ## Conditional handshake edge bounds -/

theorem rankThree_edges_le_12
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24)
    (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ p ∈ selected, p03CollisionScore .rankThree p) :
    edges ≤ 12 := by
  simpa using edges_le_of_selected_degree_sum
    (fun p : WeightThreeParameter => p03CollisionScore .rankThree p)
    selected 24 edges (rankThree_selected_sum_le_24 selected hselected) handshake

theorem rankTwo0_edges_le_12
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24)
    (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ p ∈ selected, p03CollisionScore .rankTwo0 p) :
    edges ≤ 12 := by
  simpa using edges_le_of_selected_degree_sum
    (fun p : WeightThreeParameter => p03CollisionScore .rankTwo0 p)
    selected 24 edges (rankTwo0_selected_sum_le_24 selected hselected) handshake

theorem rankTwo1_edges_le_13
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24)
    (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ p ∈ selected, p03CollisionScore .rankTwo1 p) :
    edges ≤ 13 := by
  simpa using edges_le_of_selected_degree_sum
    (fun p : WeightThreeParameter => p03CollisionScore .rankTwo1 p)
    selected 26 edges (rankTwo1_selected_sum_le_26 selected hselected) handshake

theorem rankTwo2_edges_le_28
    (selected : Finset WeightThreeParameter) (hselected : selected.card ≤ 24)
    (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ p ∈ selected, p03CollisionScore .rankTwo2 p) :
    edges ≤ 28 := by
  simpa using edges_le_of_selected_degree_sum
    (fun p : WeightThreeParameter => p03CollisionScore .rankTwo2 p)
    selected 56 edges (rankTwo2_selected_sum_le_56 selected hselected) handshake

/-! ## Uniform normal-form conclusion -/

/-- Every checked p03 normal form satisfies the collision-edge upper bound
recorded by the arithmetic layer. -/
theorem p03_edges_le_collisionUpperBound
    (form : P03NormalForm) (selected : Finset WeightThreeParameter)
    (hselected : selected.card ≤ 24) (edges : ℕ)
    (handshake : 2 * edges ≤
      ∑ p ∈ selected, p03CollisionScore form p) :
    edges ≤ p03CollisionUpperBound form := by
  cases form with
  | rankTwo0 =>
      simpa [p03CollisionUpperBound] using
        rankTwo0_edges_le_12 selected hselected edges handshake
  | rankTwo1 =>
      simpa [p03CollisionUpperBound] using
        rankTwo1_edges_le_13 selected hselected edges handshake
  | rankTwo2 =>
      simpa [p03CollisionUpperBound] using
        rankTwo2_edges_le_28 selected hselected edges handshake
  | rankThree =>
      simpa [p03CollisionUpperBound] using
        rankThree_edges_le_12 selected hselected edges handshake

/-- The checked normal-form upper bound contradicts the p03 incidence lower
bound of thirty edges. -/
theorem p03_checked_collision_contradiction
    (form : P03NormalForm) (selected : Finset WeightThreeParameter)
    (hselected : selected.card ≤ 24) (edges : ℕ)
    (lower : 30 ≤ edges)
    (handshake : 2 * edges ≤
      ∑ p ∈ selected, p03CollisionScore form p) : False := by
  exact p03_collision_contradiction form edges lower
    (p03_edges_le_collisionUpperBound form selected hselected edges handshake)

end Quantum1435
