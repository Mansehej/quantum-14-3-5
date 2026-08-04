import Quantum1435.P03ShadowIncidence
import Quantum1435.P03ShadowPairs
import Mathlib.Tactic

/-!
# Oriented shared-bin pairs in the actual p03 shadow

The incidence lower bound counts an ordered pair once for every common
coordinate/nonidentity-label bin. This file turns that sum into the
cardinality of a literal finite set of ordered pairs of actual shadow words.

The load-bearing point is that two distinct weight-three shadow words have
at most one common bin when `A₁ = A₂ = 0`. Thus the off-diagonal occupant
sets belonging to distinct bins are pairwise disjoint, and
`Finset.card_biUnion` applies without quotienting or multiplicity.
-/

noncomputable section

namespace Quantum1435

open scoped BigOperators

/-- The selected computational words occupying a fixed p03 bin. -/
def p03BinOccupants (selected : Finset CollisionWord) (bin : P03Bin) :
    Finset CollisionWord :=
  selected.filter fun word ↦ p03WordIncident word bin

@[simp] theorem mem_p03BinOccupants
    (selected : Finset CollisionWord) (bin : P03Bin) (word : CollisionWord) :
    word ∈ p03BinOccupants selected bin ↔
      word ∈ selected ∧ p03WordIncident word bin := by
  simp [p03BinOccupants]

@[simp] theorem card_p03BinOccupants
    (selected : Finset CollisionWord) (bin : P03Bin) :
    (p03BinOccupants selected bin).card =
      incidenceOccupancy selected p03WordIncident bin := by
  rfl

/-- The ordered distinct pairs of actual shadow words occupying one bin. -/
noncomputable def p03ShadowPairsAtBin
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (bin : P03Bin) : Finset (CollisionWord × CollisionWord) :=
  (p03BinOccupants (p03ShadowCollisionWords S hiso) bin).offDiag

/-- The literal finite set of ordered distinct actual shadow-word pairs
which share a nonidentity coordinate/label bin. -/
noncomputable def p03ShadowSharedPairs
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    Finset (CollisionWord × CollisionWord) :=
  p03AvailableBins.biUnion (p03ShadowPairsAtBin S hiso)

namespace LocalPauli

/-- Decoding a bit pair is nonidentity exactly when the pair is nonzero. -/
@[simp] theorem ofBits_ne_I_iff (p : F₂ × F₂) :
    ofBits p ≠ .I ↔ p ≠ 0 := by
  rcases p with ⟨x, z⟩
  fin_cases x <;> fin_cases z <;> decide

end LocalPauli

namespace CollisionWord

/-- Membership in the bin set of a decoded Pauli word, stated at the
semantic coordinate and label. -/
@[simp] theorem mem_wordBins_ofPauli_iff (u : Pauli 14) (bin : P03Bin) :
    bin ∈ (ofPauli u).wordBins ↔
      u bin.1 ≠ 0 ∧ LocalPauli.ofBits (u bin.1) = bin.2 := by
  constructor
  · intro hbin
    rcases (mem_wordBins_iff (ofPauli u) bin).mp hbin with
      ⟨i, hi, hibin⟩
    have hcoord : i = bin.1 := congrArg Prod.fst hibin
    subst i
    have hlabel : LocalPauli.ofBits (u bin.1) = bin.2 := by
      simpa [ofPauli] using congrArg Prod.snd hibin
    exact ⟨by simpa [ofPauli] using hi, hlabel⟩
  · rintro ⟨hnonzero, hlabel⟩
    apply (mem_wordBins_iff (ofPauli u) bin).mpr
    refine ⟨bin.1, ?_, ?_⟩
    · simpa [ofPauli] using hnonzero
    · exact Prod.ext rfl hlabel

end CollisionWord

/-- Common coordinate/label bins of two decoded Pauli words are counted
exactly by semantic category `C`. -/
theorem card_wordBins_inter_ofPauli_eq_p03CategoryC (u v : Pauli 14) :
    ((CollisionWord.ofPauli u).wordBins ∩
      (CollisionWord.ofPauli v).wordBins).card = p03CategoryC u v := by
  let matching : Finset (Fin 14) :=
    Finset.univ.filter fun i ↦ u i ≠ 0 ∧ u i = v i
  let matchingBin : Fin 14 → P03Bin :=
    fun i ↦ (i, LocalPauli.ofBits (u i))
  have hinjective : Function.Injective matchingBin := by
    intro i j hij
    exact congrArg Prod.fst hij
  have hintersection :
      (CollisionWord.ofPauli u).wordBins ∩
          (CollisionWord.ofPauli v).wordBins =
        matching.image matchingBin := by
    ext bin
    constructor
    · intro hbin
      have hboth := Finset.mem_inter.mp hbin
      have hu := (CollisionWord.mem_wordBins_ofPauli_iff u bin).mp hboth.1
      have hv := (CollisionWord.mem_wordBins_ofPauli_iff v bin).mp hboth.2
      have huv : u bin.1 = v bin.1 := by
        have hlabels :
            LocalPauli.ofBits (u bin.1) =
              LocalPauli.ofBits (v bin.1) := hu.2.trans hv.2.symm
        have hbits := congrArg LocalPauli.toBits hlabels
        simpa using hbits
      apply Finset.mem_image.mpr
      refine ⟨bin.1, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hu.1, huv⟩
      · exact Prod.ext rfl hu.2
    · intro hbin
      rcases Finset.mem_image.mp hbin with ⟨i, hi, hibin⟩
      have hiData := (Finset.mem_filter.mp hi).2
      rw [← hibin]
      apply Finset.mem_inter.mpr
      constructor
      · exact (CollisionWord.mem_wordBins_ofPauli_iff u
          (matchingBin i)).mpr ⟨hiData.1, rfl⟩
      · apply (CollisionWord.mem_wordBins_ofPauli_iff v
          (matchingBin i)).mpr
        constructor
        · intro hvzero
          apply hiData.1
          rw [hiData.2, hvzero]
        · simp [matchingBin, hiData.2]
  calc
    ((CollisionWord.ofPauli u).wordBins ∩
        (CollisionWord.ofPauli v).wordBins).card =
        (matching.image matchingBin).card := congrArg Finset.card hintersection
    _ = matching.card :=
      Finset.card_image_of_injective matching hinjective
    _ = p03CategoryC u v := by
      simp [matching, p03CategoryC]

/-- The off-diagonal pair sets associated with distinct bins are disjoint.
This is where the semantic `C ≤ 1` theorem is used. -/
theorem p03ShadowPairsAtBin_pairwiseDisjoint
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0) :
    (p03AvailableBins : Set P03Bin).PairwiseDisjoint
      (p03ShadowPairsAtBin S hcandidate.2.1) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro bin _ mateBin _ hcommon
  rcases hcommon with ⟨pair, hpair⟩
  rcases pair with ⟨word, mate⟩
  have hpairBoth := Finset.mem_inter.mp hpair
  have hpairBin :
      (word, mate) ∈
        (p03BinOccupants
          (p03ShadowCollisionWords S hcandidate.2.1) bin).offDiag := by
    simpa [p03ShadowPairsAtBin] using hpairBoth.1
  have hpairMateBin :
      (word, mate) ∈
        (p03BinOccupants
          (p03ShadowCollisionWords S hcandidate.2.1) mateBin).offDiag := by
    simpa [p03ShadowPairsAtBin] using hpairBoth.2
  obtain ⟨hwordBin, hmateBin, hwordNeMate⟩ :=
    Finset.mem_offDiag.mp hpairBin
  obtain ⟨hwordMateBin, hmateMateBin, _⟩ :=
    Finset.mem_offDiag.mp hpairMateBin
  have hwordBinData := (mem_p03BinOccupants _ _ _).mp hwordBin
  have hmateBinData := (mem_p03BinOccupants _ _ _).mp hmateBin
  have hwordMateBinData :=
    (mem_p03BinOccupants _ _ _).mp hwordMateBin
  have hmateMateBinData :=
    (mem_p03BinOccupants _ _ _).mp hmateMateBin
  rcases Finset.mem_image.mp hwordBinData.1 with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hmateBinData.1 with ⟨v, hv, rfl⟩
  have huv : u ≠ v := by
    intro huv
    apply hwordNeMate
    exact congrArg CollisionWord.ofPauli huv
  have hcategory :=
    p03CategoryC_le_one_of_distinct_weightThreeShadowWords
      S hcandidate hA1 hA2 hu hv huv
  have hbinInter :
      bin ∈ (CollisionWord.ofPauli u).wordBins ∩
        (CollisionWord.ofPauli v).wordBins :=
    Finset.mem_inter.mpr ⟨hwordBinData.2, hmateBinData.2⟩
  have hmateBinInter :
      mateBin ∈ (CollisionWord.ofPauli u).wordBins ∩
        (CollisionWord.ofPauli v).wordBins :=
    Finset.mem_inter.mpr
      ⟨hwordMateBinData.2, hmateMateBinData.2⟩
  by_contra hbinsNe
  have hcardGreater :
      1 < ((CollisionWord.ofPauli u).wordBins ∩
        (CollisionWord.ofPauli v).wordBins).card :=
    Finset.one_lt_card.mpr
      ⟨bin, hbinInter, mateBin, hmateBinInter, hbinsNe⟩
  rw [card_wordBins_inter_ofPauli_eq_p03CategoryC] at hcardGreater
  omega

/-- Because the per-bin pair sets are disjoint, the cardinality of the
literal shared-pair set is the ordered occupancy-product sum. -/
theorem card_p03ShadowSharedPairs_eq_incidenceOccupancy_sum
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0) :
    (p03ShadowSharedPairs S hcandidate.2.1).card =
      ∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin - 1) := by
  calc
    (p03ShadowSharedPairs S hcandidate.2.1).card =
        (p03AvailableBins.biUnion
          (p03ShadowPairsAtBin S hcandidate.2.1)).card := rfl
    _ = ∑ bin ∈ p03AvailableBins,
        (p03ShadowPairsAtBin S hcandidate.2.1 bin).card :=
      Finset.card_biUnion
        (p03ShadowPairsAtBin_pairwiseDisjoint S hcandidate hA1 hA2)
    _ = ∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin - 1) := by
      apply Finset.sum_congr rfl
      intro bin _
      simp only [p03ShadowPairsAtBin, Finset.offDiag_card,
        card_p03BinOccupants]
      rw [Nat.mul_sub_left_distrib, mul_one]

/-- In the semantic p03 profile, the actual shadow contains at least sixty
oriented distinct pairs which share a bin. -/
theorem sixty_le_card_p03ShadowSharedPairs
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    60 ≤ (p03ShadowSharedPairs S hcandidate.2.1).card := by
  have hA1 : weightDistribution S 1 = 0 :=
    (oddCandidate_profile_trichotomy S hcandidate hodd).1
  calc
    60 ≤ ∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin - 1) :=
      p03Shadow_incidenceOccupancy_lower
        S hcandidate hodd hA2 hA4 hrows
    _ = (p03ShadowSharedPairs S hcandidate.2.1).card :=
      (card_p03ShadowSharedPairs_eq_incidenceOccupancy_sum
        S hcandidate hA1 hA2).symm

end Quantum1435
