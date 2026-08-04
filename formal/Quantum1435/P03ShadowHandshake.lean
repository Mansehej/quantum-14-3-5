import Quantum1435.P03ShadowSharedPairs
import Quantum1435.P03ShadowPairs
import Quantum1435.P03CollisionAnalytic
import Mathlib.Tactic

/-!
# The semantic p03 collision handshake

This module turns the incidence lower bound for the actual weight-three
shadow into a lower bound for the collision degrees against the three actual
weight-four stabilizer translations.

The source of the injection is a literal finite set of triples
`(bin, word, mate)`. For a fixed bin, `mate` is selected from the occupants
with `word` erased, so its cardinality is definitionally the ordered
occupancy product. The target records `(word, word + mate)`. Fixed-left
addition recovers `mate`, and the previously proved `C <= 1` result recovers
the common bin. Thus no quotient, multiset certificate, or choice of a
canonical weight-three parameter is involved.
-/

noncomputable section

namespace Quantum1435

open scoped BigOperators

/-- A bin together with an ordered pair of computational shadow words. -/
abbrev P03OrientedSharedBinIncidence :=
  Sigma fun _bin : P03Bin => Sigma fun _word : CollisionWord => CollisionWord

/-- The literal bin-tagged ordered distinct pairs of actual shadow words.

The nested `sigma`/`erase` representation is chosen so that its cardinality
is the ordered occupancy sum without any inclusion-exclusion argument. -/
noncomputable def p03OrientedSharedBinIncidences
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    Finset P03OrientedSharedBinIncidence :=
  p03AvailableBins.sigma fun bin =>
    let occupants :=
      p03BinOccupants (p03ShadowCollisionWords S hiso) bin
    occupants.sigma fun word => occupants.erase word

/-- Concrete membership data for a bin-tagged ordered shadow pair. -/
theorem mem_p03OrientedSharedBinIncidences_mk
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (bin : P03Bin) (word mate : CollisionWord) :
    (Sigma.mk bin (Sigma.mk word mate) : P03OrientedSharedBinIncidence) ∈
        p03OrientedSharedBinIncidences S hiso ↔
      bin ∈ p03AvailableBins ∧
      word ∈ p03ShadowCollisionWords S hiso ∧
      p03WordIncident word bin ∧
      mate ∈ p03ShadowCollisionWords S hiso ∧
      p03WordIncident mate bin ∧
      mate ≠ word := by
  classical
  constructor
  · intro hmem
    have houter := Finset.mem_sigma.mp hmem
    have hinner := Finset.mem_sigma.mp houter.2
    have hmate := Finset.mem_erase.mp hinner.2
    have hwordData := (mem_p03BinOccupants _ _ _).mp hinner.1
    have hmateData := (mem_p03BinOccupants _ _ _).mp hmate.2
    exact ⟨houter.1, hwordData.1, hwordData.2,
      hmateData.1, hmateData.2, hmate.1⟩
  · rintro ⟨hbin, hword, hwordBin, hmate, hmateBin, hne⟩
    apply Finset.mem_sigma.mpr
    refine ⟨hbin, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩
    · exact (mem_p03BinOccupants _ _ _).mpr ⟨hword, hwordBin⟩
    · exact Finset.mem_erase.mpr
        ⟨hne, (mem_p03BinOccupants _ _ _).mpr ⟨hmate, hmateBin⟩⟩

/-- The sigma/erase source has exactly the ordered occupancy-product
cardinality used by the incidence lower bound. -/
theorem card_p03OrientedSharedBinIncidences_eq_incidenceOccupancy_sum
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    (p03OrientedSharedBinIncidences S hiso).card =
      ∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hiso) p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hiso) p03WordIncident bin - 1) := by
  classical
  rw [p03OrientedSharedBinIncidences, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro bin _
  let occupants :=
    p03BinOccupants (p03ShadowCollisionWords S hiso) bin
  change (occupants.sigma fun word => occupants.erase word).card =
    incidenceOccupancy
        (p03ShadowCollisionWords S hiso) p03WordIncident bin *
      (incidenceOccupancy
        (p03ShadowCollisionWords S hiso) p03WordIncident bin - 1)
  rw [Finset.card_sigma]
  calc
    (∑ word ∈ occupants, (occupants.erase word).card) =
        ∑ _word ∈ occupants, (occupants.card - 1) := by
      apply Finset.sum_congr rfl
      intro word hword
      exact Finset.card_erase_of_mem hword
    _ = occupants.card * (occupants.card - 1) := by simp
    _ = incidenceOccupancy
          (p03ShadowCollisionWords S hiso) p03WordIncident bin *
        (incidenceOccupancy
          (p03ShadowCollisionWords S hiso) p03WordIncident bin - 1) := by
      rw [card_p03BinOccupants]

/-- Computational shadow membership is exactly semantic shadow membership
after applying the explicit representation equivalence. -/
theorem mem_p03ShadowCollisionWords_iff_toPauli
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (word : CollisionWord) :
    word ∈ p03ShadowCollisionWords S hiso ↔
      CollisionWord.toPauli word ∈ weightThreeShadowWords S hiso := by
  classical
  constructor
  · intro hword
    rcases Finset.mem_image.mp hword with ⟨u, hu, huw⟩
    rw [← huw, CollisionWord.toPauli_ofPauli]
    exact hu
  · intro hword
    exact Finset.mem_image.mpr
      ⟨CollisionWord.toPauli word, hword,
        CollisionWord.ofPauli_toPauli word⟩

namespace CollisionWord

/-- Every computational Pauli word is its own additive inverse. -/
@[simp] theorem add_left_self (word mate : CollisionWord) :
    add word (add word mate) = mate := by
  funext i
  change LocalPauli.add (word i) (LocalPauli.add (word i) (mate i)) = mate i
  cases hword : word i <;> cases hmate : mate i <;> decide

/-- Addition by a fixed computational Pauli word is injective. -/
theorem add_left_injective (word : CollisionWord) :
    Function.Injective (add word) := by
  intro mate other hsum
  calc
    mate = add word (add word mate) := (add_left_self word mate).symm
    _ = add word (add word other) := congrArg (add word) hsum
    _ = other := add_left_self word other

end CollisionWord

/-- A common member of the literal word-bin sets witnesses the checker's
boolean `sharesBin` predicate. -/
theorem sharesBin_eq_true_of_common_wordBin
    {word mate : CollisionWord} {bin : P03Bin}
    (hword : bin ∈ word.wordBins) (hmate : bin ∈ mate.wordBins) :
  sharesBin word mate = true := by
  rcases (CollisionWord.mem_wordBins_iff word bin).mp hword with
    ⟨i, _hi, hibin⟩
  rcases (CollisionWord.mem_wordBins_iff mate bin).mp hmate with
    ⟨j, _hj, hjbin⟩
  have hij : i = j := congrArg Prod.fst (hibin.trans hjbin.symm)
  subst j
  have hlabels : word i = mate i :=
    congrArg Prod.snd (hibin.trans hjbin.symm)
  unfold sharesBin
  rw [List.any_eq_true]
  refine ⟨true, ?_, rfl⟩
  rw [List.mem_ofFn]
  exact ⟨i, by simp [_hj, hlabels]⟩

/-- If `mate` has weight three and shares a bin with `word`, translation by
`word + mate` is a collision at `word`. -/
theorem isCollision_add_of_weight_three_of_common_wordBin
    {word mate : CollisionWord} {bin : P03Bin}
    (hmateWeight : CollisionWord.weight mate = 3)
    (hword : bin ∈ word.wordBins) (hmate : bin ∈ mate.wordBins) :
    IsCollision word (CollisionWord.add word mate) := by
  have hshares := sharesBin_eq_true_of_common_wordBin hword hmate
  unfold IsCollision collisionTest
  simp [hmateWeight, hshares]

/-- The three explicit computational representatives of an exhaustive
semantic weight-four stabilizer triple. -/
def p03TranslationTriple (a b c : Pauli 14) : Finset CollisionWord :=
  {CollisionWord.ofPauli a, CollisionWord.ofPauli b,
    CollisionWord.ofPauli c}

/-- A word and one of the explicit translations which collides with it. -/
abbrev P03TripleCollisionIncidence :=
  Sigma fun _word : CollisionWord => CollisionWord

/-- The literal collision incidences against an explicit translation
triple. -/
noncomputable def p03TripleCollisionIncidences
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (a b c : Pauli 14) : Finset P03TripleCollisionIncidence :=
  (p03ShadowCollisionWords S hiso).sigma fun word =>
    (p03TranslationTriple a b c).filter fun translation =>
      IsCollision word translation

/-- For distinct translations, the target incidence cardinality is the sum
of the checker's list-valued collision degrees. -/
theorem card_p03TripleCollisionIncidences_eq_collisionDegree_sum
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    {a b c : Pauli 14} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (p03TripleCollisionIncidences S hiso a b c).card =
      ∑ word ∈ p03ShadowCollisionWords S hiso,
        collisionDegree word
          [CollisionWord.ofPauli a, CollisionWord.ofPauli b,
            CollisionWord.ofPauli c] := by
  classical
  rw [p03TripleCollisionIncidences, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro word _
  have hab' : CollisionWord.ofPauli a ≠ CollisionWord.ofPauli b :=
    fun h => hab (CollisionWord.ofPauli_injective h)
  have hac' : CollisionWord.ofPauli a ≠ CollisionWord.ofPauli c :=
    fun h => hac (CollisionWord.ofPauli_injective h)
  have hbc' : CollisionWord.ofPauli b ≠ CollisionWord.ofPauli c :=
    fun h => hbc (CollisionWord.ofPauli_injective h)
  by_cases ha : IsCollision word (CollisionWord.ofPauli a) <;>
    by_cases hb : IsCollision word (CollisionWord.ofPauli b) <;>
    by_cases hc : IsCollision word (CollisionWord.ofPauli c) <;>
    simp [p03TranslationTriple, Finset.filter_insert,
      Finset.filter_singleton, collisionDegree, ha, hb, hc,
      hab', hac', hbc']

/-- A shared pair is translated by an actual member of an exhaustive
weight-four stabilizer triple. -/
theorem add_mem_p03TranslationTriple_of_shared_shadowWords
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    {a b c : Pauli 14}
    (hexhaust : ∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
      x = a ∨ x = b ∨ x = c)
    {word mate : CollisionWord} {bin : P03Bin}
    (hword : word ∈ p03ShadowCollisionWords S hcandidate.2.1)
    (hmate : mate ∈ p03ShadowCollisionWords S hcandidate.2.1)
    (hne : word ≠ mate)
    (hwordBin : bin ∈ word.wordBins)
    (hmateBin : bin ∈ mate.wordBins) :
    CollisionWord.add word mate ∈ p03TranslationTriple a b c := by
  have hwordSemantic :=
    (mem_p03ShadowCollisionWords_iff_toPauli
      S hcandidate.2.1 word).mp hword
  have hmateSemantic :=
    (mem_p03ShadowCollisionWords_iff_toPauli
      S hcandidate.2.1 mate).mp hmate
  have hsemanticNe :
      CollisionWord.toPauli word ≠ CollisionWord.toPauli mate := by
    intro heq
    exact hne (CollisionWord.pauliEquiv.injective heq)
  have hwordBin' :
      bin ∈ (CollisionWord.ofPauli
        (CollisionWord.toPauli word)).wordBins := by
    simpa using hwordBin
  have hmateBin' :
      bin ∈ (CollisionWord.ofPauli
        (CollisionWord.toPauli mate)).wordBins := by
    simpa using hmateBin
  have hmatching :
      0 < p03CategoryC (CollisionWord.toPauli word)
        (CollisionWord.toPauli mate) := by
    rw [← card_wordBins_inter_ofPauli_eq_p03CategoryC]
    exact Finset.card_pos.mpr
      ⟨bin, Finset.mem_inter.mpr ⟨hwordBin', hmateBin'⟩⟩
  have hsum :=
    add_mem_stabilizer_and_weight_four_of_matching_shadowWords
      S hcandidate hA1 hA2 hA3 hwordSemantic hmateSemantic
        hsemanticNe hmatching
  have htranslation :
      CollisionWord.add word mate =
        CollisionWord.ofPauli
          (CollisionWord.toPauli word + CollisionWord.toPauli mate) := by
    rw [CollisionWord.ofPauli_add, CollisionWord.ofPauli_toPauli,
      CollisionWord.ofPauli_toPauli]
  rw [htranslation]
  rcases (hexhaust _).mp hsum with ha | hb | hc
  · rw [ha]
    simp [p03TranslationTriple]
  · rw [hb]
    simp [p03TranslationTriple]
  · rw [hc]
    simp [p03TranslationTriple]

/-- The bin-tagged shared-pair set injects into the collision incidences
against an exhaustive actual weight-four translation triple. -/
theorem card_p03OrientedSharedBinIncidences_le_tripleCollisionIncidences
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    {a b c : Pauli 14}
    (hexhaust : ∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
      x = a ∨ x = b ∨ x = c) :
    (p03OrientedSharedBinIncidences S hcandidate.2.1).card ≤
      (p03TripleCollisionIncidences S hcandidate.2.1 a b c).card := by
  classical
  let mapIncidence :
      P03OrientedSharedBinIncidence → P03TripleCollisionIncidence :=
    fun item => Sigma.mk item.2.1
      (CollisionWord.add item.2.1 item.2.2)
  apply Finset.card_le_card_of_injOn mapIncidence
  · intro item hitem
    rcases item with ⟨bin, pair⟩
    rcases pair with ⟨word, mate⟩
    rcases (mem_p03OrientedSharedBinIncidences_mk
      S hcandidate.2.1 bin word mate).mp hitem with
      ⟨_hbin, hword, hwordBin, hmate, hmateBin, hmateNe⟩
    apply Finset.mem_sigma.mpr
    refine ⟨hword, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact add_mem_p03TranslationTriple_of_shared_shadowWords
        S hcandidate hA1 hA2 hA3 hexhaust hword hmate
          hmateNe.symm hwordBin hmateBin
    · have hmateSemantic :=
        (mem_p03ShadowCollisionWords_iff_toPauli
          S hcandidate.2.1 mate).mp hmate
      have hmateWeight : CollisionWord.weight mate = 3 := by
        rw [CollisionWord.weight_eq_pauliWeight]
        exact (mem_weightThreeShadowWords
          S hcandidate.2.1 (CollisionWord.toPauli mate)).mp
            hmateSemantic |>.2
      change IsCollision word (CollisionWord.add word mate)
      exact isCollision_add_of_weight_three_of_common_wordBin
        hmateWeight hwordBin hmateBin
  · intro left hleft right hright heq
    rcases left with ⟨leftBin, leftPair⟩
    rcases leftPair with ⟨word, mate⟩
    rcases right with ⟨rightBin, rightPair⟩
    rcases rightPair with ⟨otherWord, otherMate⟩
    rcases (mem_p03OrientedSharedBinIncidences_mk
      S hcandidate.2.1 leftBin word mate).mp hleft with
      ⟨_hleftBin, hword, hwordBin, hmate, hmateBin, hmateNe⟩
    rcases (mem_p03OrientedSharedBinIncidences_mk
      S hcandidate.2.1 rightBin otherWord otherMate).mp hright with
      ⟨_hrightBin, hotherWord, hotherWordBin,
        hotherMate, hotherMateBin, _hotherMateNe⟩
    have hwordEq : word = otherWord :=
      congrArg Sigma.fst heq
    subst otherWord
    have htranslationEq :
        CollisionWord.add word mate =
          CollisionWord.add word otherMate :=
      congrArg (fun item : P03TripleCollisionIncidence => item.2) heq
    have hmateEq : mate = otherMate :=
      CollisionWord.add_left_injective word htranslationEq
    subst otherMate
    have hwordSemantic :=
      (mem_p03ShadowCollisionWords_iff_toPauli
        S hcandidate.2.1 word).mp hword
    have hmateSemantic :=
      (mem_p03ShadowCollisionWords_iff_toPauli
        S hcandidate.2.1 mate).mp hmate
    have hsemanticNe :
        CollisionWord.toPauli word ≠ CollisionWord.toPauli mate := by
      intro hsame
      exact hmateNe
        (CollisionWord.pauliEquiv.injective hsame).symm
    have hcategory :=
      p03CategoryC_le_one_of_distinct_weightThreeShadowWords
        S hcandidate hA1 hA2 hwordSemantic hmateSemantic hsemanticNe
    have hcommonCard :
        (word.wordBins ∩ mate.wordBins).card ≤ 1 := by
      calc
        (word.wordBins ∩ mate.wordBins).card =
            ((CollisionWord.ofPauli
                (CollisionWord.toPauli word)).wordBins ∩
              (CollisionWord.ofPauli
                (CollisionWord.toPauli mate)).wordBins).card := by simp
        _ = p03CategoryC (CollisionWord.toPauli word)
              (CollisionWord.toPauli mate) :=
          card_wordBins_inter_ofPauli_eq_p03CategoryC _ _
        _ ≤ 1 := hcategory
    have hleftBinMem : leftBin ∈ word.wordBins ∩ mate.wordBins :=
      Finset.mem_inter.mpr ⟨hwordBin, hmateBin⟩
    have hrightBinMem : rightBin ∈ word.wordBins ∩ mate.wordBins :=
      Finset.mem_inter.mpr ⟨hotherWordBin, hotherMateBin⟩
    have hbinEq : leftBin = rightBin :=
      (Finset.card_le_one.mp hcommonCard)
        leftBin hleftBinMem rightBin hrightBinMem
    subst rightBin
    rfl

/-- The actual p03 shadow contributes at least sixty collision incidences
against any explicit exhaustive listing of the three weight-four stabilizer
translations. -/
theorem p03Shadow_collisionDegree_triple_lower
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1)
    {a b c : Pauli 14}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hexhaust : ∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
      x = a ∨ x = b ∨ x = c) :
    60 ≤ ∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
      collisionDegree word
        [CollisionWord.ofPauli a, CollisionWord.ofPauli b,
          CollisionWord.ofPauli c] := by
  calc
    60 ≤ ∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
              p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
              p03WordIncident bin - 1) :=
      p03Shadow_incidenceOccupancy_lower
        S hcandidate hodd hA2 hA4 hrows
    _ = (p03OrientedSharedBinIncidences S hcandidate.2.1).card :=
      (card_p03OrientedSharedBinIncidences_eq_incidenceOccupancy_sum
        S hcandidate.2.1).symm
    _ ≤ (p03TripleCollisionIncidences
        S hcandidate.2.1 a b c).card :=
      card_p03OrientedSharedBinIncidences_le_tripleCollisionIncidences
        S hcandidate hA1 hA2 hA3 hexhaust
    _ = ∑ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
        collisionDegree word
          [CollisionWord.ofPauli a, CollisionWord.ofPauli b,
            CollisionWord.ofPauli c] :=
      card_p03TripleCollisionIncidences_eq_collisionDegree_sum
        S hcandidate.2.1 hab hac hbc

end Quantum1435
