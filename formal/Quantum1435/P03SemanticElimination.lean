import Quantum1435.P03SemanticGeometry
import Quantum1435.P03ShadowHandshake
import Quantum1435.P03RankTwoInvariantBounds
import Quantum1435.OddUniversalSemantic
import Mathlib.Tactic

/-!
# Semantic elimination of three p03 weight-four geometries

This module compares the sixty collision incidences forced by the actual
weight-three shadow with representative-free upper bounds for an exhaustive
triple of actual weight-four stabilizer words. The rank-two `p = 0` and
rank-three alternatives have degree sum at most 24, while rank-two `p = 2`
has degree sum at most 56. Consequently only rank-two `p = 1` can occur.

The conditional geometry lemmas retain the `SemanticOddUniversalRows`
interface, while the final theorem supplies it from the literal signed-shadow
transform.
-/

noncomputable section

namespace Quantum1435

open scoped BigOperators

/-- Every computational representative of an actual weight-three shadow
word has computational weight three. -/
private theorem p03ShadowCollisionWord_weight_three
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (word : CollisionWord) (hword : word ∈ p03ShadowCollisionWords S hiso) :
    CollisionWord.weight word = 3 := by
  simpa using p03ShadowCollisionWords_card_wordBins S hiso word hword

/-- An exhaustive distinct actual weight-four triple with one of the four
invariant geometries must have the rank-two `p = 1` category data. -/
theorem p03TripleGeometry_forces_rankTwo1
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1)
    {u v w : Pauli 14}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hexhaust : ∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
      x = u ∨ x = v ∨ x = w)
    (hgeometry : P03TripleGeometry u v w) :
    u + v = w ∧
      p03CategoryA u v = 1 ∧
      p03CategoryB u v = 1 ∧
      p03CategoryC u v = 1 ∧
      p03CategoryD u v = 2 := by
  have huData : u ∈ S ∧ pauliWeight u = 4 :=
    (hexhaust u).mpr (Or.inl rfl)
  have hvData : v ∈ S ∧ pauliWeight v = 4 :=
    (hexhaust v).mpr (Or.inr (Or.inl rfl))
  have hwData : w ∈ S ∧ pauliWeight w = 4 :=
    (hexhaust w).mpr (Or.inr (Or.inr rfl))
  have hprofile := oddCandidate_profile_trichotomy S hcandidate hodd
  have hA1 : weightDistribution S 1 = 0 := hprofile.1
  have hA3 : weightDistribution S 3 = 0 := hprofile.2.1
  have hselected :
      (p03ShadowCollisionWords S hcandidate.2.1).card ≤ 24 := by
    rw [p03ShadowCollisionWords_card_eq_24
      S hcandidate hodd hA2 hA4 hrows]
  have hword : ∀ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
      CollisionWord.weight word = 3 := by
    intro word hword
    exact p03ShadowCollisionWord_weight_three
      S hcandidate.2.1 word hword
  have hlower :
      60 ≤ ∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
        collisionDegree word
          [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
            CollisionWord.ofPauli w] :=
    p03Shadow_collisionDegree_triple_lower
      S hcandidate hodd hA1 hA2 hA3 hA4 hrows
        huv huw hvw hexhaust
  cases hgeometry with
  | rankTwo0 hsum hA hB hC _hD =>
      have hadd :
          CollisionWord.add (CollisionWord.ofPauli u)
              (CollisionWord.ofPauli v) =
            CollisionWord.ofPauli w := by
        rw [← CollisionWord.ofPauli_add, hsum]
      have hupper :
          (∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
            collisionDegree word
              [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
                CollisionWord.ofPauli w]) ≤ 24 := by
        simpa [hadd] using
          (rankTwo_p0_selected_degree_sum_le_twenty_four
            (u := CollisionWord.ofPauli u)
            (v := CollisionWord.ofPauli v)
            (p03ShadowCollisionWords S hcandidate.2.1)
            hselected hword
            (by simpa using huData.2)
            (by simpa using hvData.2)
            (by simpa [hadd] using hwData.2)
            (by simpa using hA)
            (by simpa using hB)
            (by simpa using hC))
      omega
  | rankTwo1 hsum hA hB hC hD =>
      exact ⟨hsum, hA, hB, hC, hD⟩
  | rankTwo2 hsum hA hB hC hD =>
      have hadd :
          CollisionWord.add (CollisionWord.ofPauli u)
              (CollisionWord.ofPauli v) =
            CollisionWord.ofPauli w := by
        rw [← CollisionWord.ofPauli_add, hsum]
      have hupper :
          (∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
            collisionDegree word
              [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
                CollisionWord.ofPauli w]) ≤ 56 := by
        simpa [hadd] using
          (rankTwo_p2_selected_degree_sum_le_56
            (u := CollisionWord.ofPauli u)
            (v := CollisionWord.ofPauli v)
            (p03ShadowCollisionWords S hcandidate.2.1)
            hselected hword
            (by simpa using huData.2)
            (by simpa using hvData.2)
            (by simpa [hadd] using hwData.2)
            (by simpa using hA)
            (by simpa using hB)
            (by simpa using hC)
            (by simpa using hD))
      omega
  | rankThree hdisjointUV hdisjointUW hdisjointVW =>
      have htranslation : ∀ translation ∈
          [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
            CollisionWord.ofPauli w],
          CollisionWord.weight translation = 4 := by
        intro translation htranslation
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htranslation
        rcases htranslation with rfl | rfl | rfl
        · simpa using huData.2
        · simpa using hvData.2
        · simpa using hwData.2
      have hpairwise :
          [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
            CollisionWord.ofPauli w].Pairwise fun a b ↦
              Disjoint (p03Support (CollisionWord.toPauli a))
                (p03Support (CollisionWord.toPauli b)) := by
        rw [List.pairwise_cons]
        constructor
        · intro translation htranslation
          simp only [List.mem_cons, List.not_mem_nil, or_false] at htranslation
          rcases htranslation with rfl | rfl
          · simpa using hdisjointUV
          · simpa using hdisjointUW
        · rw [List.pairwise_cons]
          constructor
          · intro translation htranslation
            simp only [List.mem_cons, List.not_mem_nil, or_false] at htranslation
            subst translation
            simpa using hdisjointVW
          · simp
      have hupper :
          (∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
            collisionDegree word
              [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
                CollisionWord.ofPauli w]) ≤ 24 :=
        selected_degree_sum_le_twenty_four_of_pairwise_disjoint_support
          (p03ShadowCollisionWords S hcandidate.2.1)
          hselected hword htranslation hpairwise
      omega

/-- Candidate-level p03 conclusion: the three actual weight-four stabilizer
words can be chosen as the nonzero elements of a rank-two `p = 1` plane. -/
theorem p03_candidate_exists_rankTwo1_weightFour_triple
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    ∃ u v w : Pauli 14,
      u ∈ S ∧ pauliWeight u = 4 ∧
      v ∈ S ∧ pauliWeight v = 4 ∧
      w ∈ S ∧ pauliWeight w = 4 ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
        x = u ∨ x = v ∨ x = w) ∧
      u + v = w ∧
      p03CategoryA u v = 1 ∧
      p03CategoryB u v = 1 ∧
      p03CategoryC u v = 1 ∧
      p03CategoryD u v = 2 := by
  obtain ⟨u, v, w, huS, huWeight, hvS, hvWeight, hwS, hwWeight,
      huv, huw, hvw, hexhaust, hgeometry⟩ :=
    p03_candidate_exists_classified_weightFour_triple
      S hcandidate hodd hA2 hA4 hrows
  have hp1 := p03TripleGeometry_forces_rankTwo1
    S hcandidate hodd hA2 hA4 hrows
      huv huw hvw hexhaust hgeometry
  exact ⟨u, v, w, huS, huWeight, hvS, hvWeight, hwS, hwWeight,
    huv, huw, hvw, hexhaust, hp1⟩

/-- The p03 profile is impossible once the two semantic odd-branch
enumerator rows have been derived. This theorem contains the complete
representative-free incidence elimination; the semantic universal rows
remain an explicit hypothesis. -/
theorem p03_candidate_false_of_semanticOddUniversalRows
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    False := by
  obtain ⟨u, v, w, huS, huWeight, hvS, hvWeight, hwS, hwWeight,
      huv, huw, hvw, hexhaust, hsum, hA, hB, hC, hD⟩ :=
    p03_candidate_exists_rankTwo1_weightFour_triple
      S hcandidate hodd hA2 hA4 hrows
  have hprofile := oddCandidate_profile_trichotomy S hcandidate hodd
  have hA1 : weightDistribution S 1 = 0 := hprofile.1
  have hA3 : weightDistribution S 3 = 0 := hprofile.2.1
  have hselected :
      (p03ShadowCollisionWords S hcandidate.2.1).card ≤ 24 := by
    rw [p03ShadowCollisionWords_card_eq_24
      S hcandidate hodd hA2 hA4 hrows]
  have hword : ∀ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
      CollisionWord.weight word = 3 := by
    intro word hword
    exact p03ShadowCollisionWord_weight_three
      S hcandidate.2.1 word hword
  have hlower :
      60 ≤ ∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
        collisionDegree word
          [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
            CollisionWord.ofPauli w] :=
    p03Shadow_collisionDegree_triple_lower
      S hcandidate hodd hA1 hA2 hA3 hA4 hrows
        huv huw hvw hexhaust
  have hadd :
      CollisionWord.add (CollisionWord.ofPauli u)
          (CollisionWord.ofPauli v) =
        CollisionWord.ofPauli w := by
    rw [← CollisionWord.ofPauli_add, hsum]
  have hupper :
      (∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
        collisionDegree word
          [CollisionWord.ofPauli u, CollisionWord.ofPauli v,
            CollisionWord.ofPauli w]) ≤ 26 := by
    simpa [hadd] using
      (rankTwo_p1_selected_degree_sum_le_26
        (u := CollisionWord.ofPauli u)
        (v := CollisionWord.ofPauli v)
        (p03ShadowCollisionWords S hcandidate.2.1)
        hselected hword
        (by simpa using huWeight)
        (by simpa using hvWeight)
        (by simpa [hadd] using hwWeight)
        (by simpa using hA)
        (by simpa using hB)
        (by simpa using hC)
        (by simpa using hD))
  omega

/-- No actual odd candidate can lie in profile `(A₂,A₄)=(0,3)`. -/
theorem p03_candidate_false
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3) :
    False :=
  p03_candidate_false_of_semanticOddUniversalRows
    S hcandidate hodd hA2 hA4
      (semanticOddUniversalRows S hcandidate hodd)

end Quantum1435
