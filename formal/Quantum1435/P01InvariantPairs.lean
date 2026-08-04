import Quantum1435.P01ShadowLowWeights
import Quantum1435.P03ShadowSharedPairs
import Quantum1435.P03ShadowHandshake
import Mathlib.Tactic

/-!
# Invariant shared-pair obstruction in the p01 profile

The external replay enumerates ninety translation orbits for the unique
weight-four stabilizer and checks all 4,005 pairs of distinct orbits.  The
load-bearing conclusion has a short representative-free proof instead.

If a weight-three word `g` and its translate `g + u` both have weight three
and share a bin, the four coordinate categories relative to the weight-four
translation `u` are forced to be `(A,B,C,D) = (1,2,2,0)`.  For two such
orbits, represented by `g` and `h`, one of the cross differences `g + h` and
`g + (h + u)` has weight at most four.  Two distinct actual shadow orbits
would therefore produce a forbidden low-weight normalizer word.

Consequently the literal set of oriented shared-bin shadow pairs has at most
two members: the two orientations of a single unordered pair.  No coordinate
normalization, local-Clifford transport, JSON certificate, or external
enumeration is used.
-/

noncomputable section

namespace Quantum1435

/-- Concrete membership in the literal oriented shared-pair set. -/
theorem mem_p03ShadowSharedPairs_iff
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (word mate : CollisionWord) :
    (word, mate) ∈ p03ShadowSharedPairs S hiso ↔
      word ∈ p03ShadowCollisionWords S hiso ∧
      mate ∈ p03ShadowCollisionWords S hiso ∧
      word ≠ mate ∧
      ∃ bin ∈ p03AvailableBins,
        p03WordIncident word bin ∧ p03WordIncident mate bin := by
  classical
  constructor
  · intro hpair
    rcases Finset.mem_biUnion.mp hpair with ⟨bin, hbin, hpairBin⟩
    have hpairBin' :
        (word, mate) ∈
          (p03BinOccupants (p03ShadowCollisionWords S hiso) bin).offDiag := by
      simpa [p03ShadowPairsAtBin] using hpairBin
    obtain ⟨hword, hmate, hne⟩ := Finset.mem_offDiag.mp hpairBin'
    have hwordData := (mem_p03BinOccupants _ _ _).mp hword
    have hmateData := (mem_p03BinOccupants _ _ _).mp hmate
    exact ⟨hwordData.1, hmateData.1, hne, bin, hbin,
      hwordData.2, hmateData.2⟩
  · rintro ⟨hword, hmate, hne, bin, hbin, hwordBin, hmateBin⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨bin, hbin, ?_⟩
    change (word, mate) ∈
      (p03BinOccupants (p03ShadowCollisionWords S hiso) bin).offDiag
    exact Finset.mem_offDiag.mpr
      ⟨(mem_p03BinOccupants _ _ _).mpr ⟨hword, hwordBin⟩,
       (mem_p03BinOccupants _ _ _).mpr ⟨hmate, hmateBin⟩, hne⟩

/-- Matching coordinates of `g` and `g + u` are precisely the nonzero
coordinates of `g` outside the support of `u`. -/
theorem p03CategoryC_self_add_eq_categoryA {n : ℕ} (g u : Pauli n) :
    p03CategoryC g (g + u) = p03CategoryA g u := by
  classical
  unfold p03CategoryC p03CategoryA
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  constructor
  · rintro ⟨hg, heq⟩
    refine ⟨hg, ?_⟩
    have hcancel : g i + 0 = g i + u i := by simpa using heq
    exact (add_left_cancel hcancel).symm
  · rintro ⟨hg, hu⟩
    exact ⟨hg, by simp [hu]⟩

/-- Outside the support of `u`, the support of `g + h` is contained in the
union of the corresponding outside supports of `g` and `h`. -/
theorem p03CategoryA_add_le (g h u : Pauli 14) :
    p03CategoryA (g + h) u ≤ p03CategoryA g u + p03CategoryA h u := by
  classical
  let sumOutside : Finset (Fin 14) :=
    Finset.univ.filter fun i ↦ (g + h) i ≠ 0 ∧ u i = 0
  let gOutside : Finset (Fin 14) :=
    Finset.univ.filter fun i ↦ g i ≠ 0 ∧ u i = 0
  let hOutside : Finset (Fin 14) :=
    Finset.univ.filter fun i ↦ h i ≠ 0 ∧ u i = 0
  have hsubset : sumOutside ⊆ gOutside ∪ hOutside := by
    intro i hi
    have hiData := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_union]
    by_cases hgi : g i = 0
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, hiData.2⟩
      intro hhi
      apply hiData.1
      simp [Pi.add_apply, hgi, hhi]
    · left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hgi, hiData.2⟩
  calc
    p03CategoryA (g + h) u = sumOutside.card := by rfl
    _ ≤ (gOutside ∪ hOutside).card := Finset.card_le_card hsubset
    _ ≤ gOutside.card + hOutside.card := Finset.card_union_le _ _
    _ = p03CategoryA g u + p03CategoryA h u := by rfl

/-- If neither `g` nor `h` ever carries a label different from the nonzero
label of `u`, neither does their sum. -/
theorem p03CategoryD_add_eq_zero {g h u : Pauli 14}
    (hg : p03CategoryD g u = 0) (hh : p03CategoryD h u = 0) :
    p03CategoryD (g + h) u = 0 := by
  classical
  rw [p03CategoryD, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hiData := (Finset.mem_filter.mp hi).2
  have hgAllowed : g i = 0 ∨ g i = u i := by
    by_cases hgi : g i = 0
    · exact Or.inl hgi
    · right
      by_contra hgiu
      have hpos : 0 < p03CategoryD g u := by
        apply Finset.card_pos.mpr
        exact ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hgi, hiData.2.1, hgiu⟩⟩
      omega
  have hhAllowed : h i = 0 ∨ h i = u i := by
    by_cases hhi : h i = 0
    · exact Or.inl hhi
    · right
      by_contra hhiu
      have hpos : 0 < p03CategoryD h u := by
        apply Finset.card_pos.mpr
        exact ⟨i, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hhi, hiData.2.1, hhiu⟩⟩
      omega
  rcases hgAllowed with hgi | hgiu
  · rcases hhAllowed with hhi | hhiu
    · exact hiData.1 (by simp [Pi.add_apply, hgi, hhi])
    · exact hiData.2.2 (by simp [Pi.add_apply, hgi, hhiu])
  · rcases hhAllowed with hhi | hhiu
    · exact hiData.2.2 (by simp [Pi.add_apply, hgiu, hhi])
    · apply hiData.1
      rw [Pi.add_apply, hgiu, hhiu]
      exact CharTwo.add_self_eq_zero (u i)

/-- Two weight-three collision orbits for one weight-four translation have a
cross difference of weight at most four. -/
theorem p01_cross_weight_le_four {g h u : Pauli 14}
    (hu : pauliWeight u = 4)
    (hg : pauliWeight g = 3) (hgu : pauliWeight (g + u) = 3)
    (hgShare : 0 < p03CategoryC g (g + u))
    (hh : pauliWeight h = 3) (hhu : pauliWeight (h + u) = 3)
    (hhShare : 0 < p03CategoryC h (h + u)) :
    pauliWeight (g + h) ≤ 4 ∨ pauliWeight (g + (h + u)) ≤ 4 := by
  rw [p03CategoryC_self_add_eq_categoryA] at hgShare hhShare
  have hgWeight := pauliWeight_eq_categories_ACD g u
  have huFromG := pauliWeight_eq_categories_BCD g u
  have hguWeight := pauliWeight_add_eq_categories_ABD g u
  rw [hg] at hgWeight
  rw [hu] at huFromG
  rw [hgu] at hguWeight
  have hgA : p03CategoryA g u = 1 := by omega
  have hgD : p03CategoryD g u = 0 := by omega
  have hhWeight := pauliWeight_eq_categories_ACD h u
  have huFromH := pauliWeight_eq_categories_BCD h u
  have hhuWeight := pauliWeight_add_eq_categories_ABD h u
  rw [hh] at hhWeight
  rw [hu] at huFromH
  rw [hhu] at hhuWeight
  have hhA : p03CategoryA h u = 1 := by omega
  have hhD : p03CategoryD h u = 0 := by omega
  have hsumA := p03CategoryA_add_le g h u
  rw [hgA, hhA] at hsumA
  have hsumD : p03CategoryD (g + h) u = 0 :=
    p03CategoryD_add_eq_zero hgD hhD
  have hsumWeight := pauliWeight_eq_categories_ACD (g + h) u
  have huFromSum := pauliWeight_eq_categories_BCD (g + h) u
  have hsumTranslated := pauliWeight_add_eq_categories_ABD (g + h) u
  rw [hsumD] at hsumWeight huFromSum hsumTranslated
  rw [hu] at huFromSum
  by_cases hlow : pauliWeight (g + h) ≤ 4
  · exact Or.inl hlow
  · right
    have : pauliWeight ((g + h) + u) ≤ 4 := by omega
    simpa only [add_assoc] using this

/-- A low-weight sum of two distinct actual shadow words is a weight-four
stabilizer word in the p01 low-weight profile. -/
private theorem p01_shadow_sum_mem_stabilizer_weight_four
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    {u v : Pauli 14}
    (hu : IsShadowWord S hcandidate.2.1 u)
    (hv : IsShadowWord S hcandidate.2.1 v)
    (huv : u ≠ v) (hweight : pauliWeight (u + v) ≤ 4) :
    u + v ∈ S ∧ pauliWeight (u + v) = 4 := by
  have hnormalizer : u + v ∈ symplecticNormalizer S :=
    shadowWord_add_shadowWord_mem_normalizer hu hv
  have hsumS : u + v ∈ S := by
    by_contra hnotS
    have hdistance : 5 ≤ pauliWeight (u + v) :=
      hcandidate.2.2 (u + v) ⟨hnormalizer, hnotS⟩
    omega
  have hneZero : pauliWeight (u + v) ≠ 0 := by
    intro hzero
    exact huv (eq_of_pauliWeight_add_eq_zero hzero)
  have hneOne : pauliWeight (u + v) ≠ 1 := by
    intro hone
    exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
  have hneTwo : pauliWeight (u + v) ≠ 2 := by
    intro htwo
    exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS
  have hneThree : pauliWeight (u + v) ≠ 3 := by
    intro hthree
    exact (not_mem_of_weightDistribution_eq_zero S hA3 hthree) hsumS
  exact ⟨hsumS, by omega⟩

/-- A common computational bin gives a positive semantic matching category. -/
private theorem p03CategoryC_pos_of_common_wordBin
    {word mate : CollisionWord} {bin : P03Bin}
    (hword : p03WordIncident word bin)
    (hmate : p03WordIncident mate bin) :
    0 < p03CategoryC (CollisionWord.toPauli word)
      (CollisionWord.toPauli mate) := by
  have hmem : bin ∈ word.wordBins ∩ mate.wordBins :=
    Finset.mem_inter.mpr ⟨hword, hmate⟩
  have hpos : 0 < (word.wordBins ∩ mate.wordBins).card :=
    Finset.card_pos.mpr ⟨bin, hmem⟩
  have hcard := card_wordBins_inter_ofPauli_eq_p03CategoryC
    (CollisionWord.toPauli word) (CollisionWord.toPauli mate)
  rw [CollisionWord.ofPauli_toPauli, CollisionWord.ofPauli_toPauli] at hcard
  omega

/-- The translation associated with a literal shared pair is an actual
weight-four stabilizer word. -/
private theorem p01_sharedPair_translation_data
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    {word mate : CollisionWord}
    (hpair : (word, mate) ∈ p03ShadowSharedPairs S hcandidate.2.1) :
    CollisionWord.toPauli (CollisionWord.add word mate) ∈ S ∧
      pauliWeight (CollisionWord.toPauli (CollisionWord.add word mate)) = 4 := by
  rcases (mem_p03ShadowSharedPairs_iff
    S hcandidate.2.1 word mate).mp hpair with
      ⟨hword, hmate, hne, bin, _hbin, hwordBin, hmateBin⟩
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
  have hcategory := p03CategoryC_pos_of_common_wordBin hwordBin hmateBin
  have hsum := add_mem_stabilizer_and_weight_four_of_matching_shadowWords
    S hcandidate hA1 hA2 hA3 hwordSemantic hmateSemantic hsemanticNe hcategory
  simpa only [CollisionWord.toPauli_add] using hsum

/-- The p01 profile permits at most one unordered shared-bin translation
pair, hence at most its two orientations in the literal pair set. -/
theorem p01_card_p03ShadowSharedPairs_le_two
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 1) :
    (p03ShadowSharedPairs S hcandidate.2.1).card ≤ 2 := by
  classical
  let pairs := p03ShadowSharedPairs S hcandidate.2.1
  change pairs.card ≤ 2
  by_cases hpairs : pairs = ∅
  · rw [hpairs]
    simp
  obtain ⟨basePair, hbasePair⟩ :=
    Finset.nonempty_iff_ne_empty.mpr hpairs
  rcases basePair with ⟨baseWord, baseMate⟩
  have hbasePair' :
      (baseWord, baseMate) ∈
        p03ShadowSharedPairs S hcandidate.2.1 := by
    simpa [pairs] using hbasePair
  rcases (mem_p03ShadowSharedPairs_iff
    S hcandidate.2.1 baseWord baseMate).mp hbasePair' with
      ⟨hbaseWord, hbaseMate, hbaseNe, baseBin, _hbaseBin,
        hbaseWordBin, hbaseMateBin⟩
  have hbaseWordSemantic :=
    (mem_p03ShadowCollisionWords_iff_toPauli
      S hcandidate.2.1 baseWord).mp hbaseWord
  have hbaseMateSemantic :=
    (mem_p03ShadowCollisionWords_iff_toPauli
      S hcandidate.2.1 baseMate).mp hbaseMate
  have hbaseWordData :=
    (mem_weightThreeShadowWords S hcandidate.2.1
      (CollisionWord.toPauli baseWord)).mp hbaseWordSemantic
  have hbaseMateData :=
    (mem_weightThreeShadowWords S hcandidate.2.1
      (CollisionWord.toPauli baseMate)).mp hbaseMateSemantic
  have hbaseWordWeight :
      pauliWeight (CollisionWord.toPauli baseWord) = 3 := hbaseWordData.2
  have hbaseMateWeight :
      pauliWeight (CollisionWord.toPauli baseMate) = 3 := hbaseMateData.2
  let translation := CollisionWord.add baseWord baseMate
  have hbaseTranslation :
      CollisionWord.toPauli translation ∈ S ∧
        pauliWeight (CollisionWord.toPauli translation) = 4 := by
    simpa [translation] using
      (p01_sharedPair_translation_data
        S hcandidate hA1 hA2 hA3 hbasePair')
  obtain ⟨uniqueFour, _huniqueFour, hunique⟩ :=
    existsUnique_of_weightDistribution_eq_one S hA4
  have hbaseUnique : CollisionWord.toPauli translation = uniqueFour :=
    hunique (CollisionWord.toPauli translation) hbaseTranslation
  have hsubset :
      pairs ⊆ {(baseWord, baseMate), (baseMate, baseWord)} := by
    intro pair hpair
    rcases pair with ⟨word, mate⟩
    have hpair' :
        (word, mate) ∈ p03ShadowSharedPairs S hcandidate.2.1 := by
      simpa [pairs] using hpair
    rcases (mem_p03ShadowSharedPairs_iff
      S hcandidate.2.1 word mate).mp hpair' with
        ⟨hword, hmate, hne, bin, _hbin, hwordBin, hmateBin⟩
    have hwordSemantic :=
      (mem_p03ShadowCollisionWords_iff_toPauli
        S hcandidate.2.1 word).mp hword
    have hmateSemantic :=
      (mem_p03ShadowCollisionWords_iff_toPauli
        S hcandidate.2.1 mate).mp hmate
    have hwordData :=
      (mem_weightThreeShadowWords S hcandidate.2.1
        (CollisionWord.toPauli word)).mp hwordSemantic
    have hmateData :=
      (mem_weightThreeShadowWords S hcandidate.2.1
        (CollisionWord.toPauli mate)).mp hmateSemantic
    have hwordWeight : pauliWeight (CollisionWord.toPauli word) = 3 :=
      hwordData.2
    have hmateWeight : pauliWeight (CollisionWord.toPauli mate) = 3 :=
      hmateData.2
    have htranslationData :=
      p01_sharedPair_translation_data S hcandidate hA1 hA2 hA3 hpair'
    have htranslationUnique :
        CollisionWord.toPauli (CollisionWord.add word mate) = uniqueFour :=
      hunique (CollisionWord.toPauli (CollisionWord.add word mate))
        htranslationData
    have htranslationSemantic :
        CollisionWord.toPauli (CollisionWord.add word mate) =
          CollisionWord.toPauli translation :=
      htranslationUnique.trans hbaseUnique.symm
    have htranslation : CollisionWord.add word mate = translation :=
      CollisionWord.pauliEquiv.injective htranslationSemantic
    by_cases hwordBase : word = baseWord
    · subst word
      have hmateBase : mate = baseMate := by
        apply CollisionWord.add_left_injective baseWord
        simpa [translation] using htranslation
      subst mate
      simp
    by_cases hwordMate : word = baseMate
    · subst word
      have hmateBase : mate = baseWord := by
        have hsemantic :
            CollisionWord.toPauli baseMate + CollisionWord.toPauli mate =
              CollisionWord.toPauli baseMate +
                CollisionWord.toPauli baseWord := by
          calc
            CollisionWord.toPauli baseMate + CollisionWord.toPauli mate =
                CollisionWord.toPauli (CollisionWord.add baseMate mate) := by
              rw [CollisionWord.toPauli_add]
            _ = CollisionWord.toPauli translation :=
              congrArg CollisionWord.toPauli htranslation
            _ = CollisionWord.toPauli baseWord +
                CollisionWord.toPauli baseMate := by
              rw [show translation = CollisionWord.add baseWord baseMate by rfl,
                CollisionWord.toPauli_add]
            _ = CollisionWord.toPauli baseMate +
                CollisionWord.toPauli baseWord := add_comm _ _
        exact CollisionWord.pauliEquiv.injective (add_left_cancel hsemantic)
      subst mate
      simp
    exfalso
    have hbaseCategory :=
      p03CategoryC_pos_of_common_wordBin hbaseWordBin hbaseMateBin
    have hwordCategory :=
      p03CategoryC_pos_of_common_wordBin hwordBin hmateBin
    have hbaseTranslated :
        CollisionWord.toPauli baseWord +
            CollisionWord.toPauli translation =
          CollisionWord.toPauli baseMate := by
      rw [← CollisionWord.toPauli_add,
        show translation = CollisionWord.add baseWord baseMate by rfl,
        CollisionWord.add_left_self]
    have hwordTranslated :
        CollisionWord.toPauli word +
            CollisionWord.toPauli translation =
          CollisionWord.toPauli mate := by
      rw [← CollisionWord.toPauli_add, ← htranslation,
        CollisionWord.add_left_self]
    have hbaseTranslatedWeight :
        pauliWeight (CollisionWord.toPauli baseWord +
          CollisionWord.toPauli translation) = 3 := by
      rw [hbaseTranslated]
      exact hbaseMateWeight
    have hbaseTranslatedCategory :
        0 < p03CategoryC (CollisionWord.toPauli baseWord)
          (CollisionWord.toPauli baseWord +
            CollisionWord.toPauli translation) := by
      rw [hbaseTranslated]
      exact hbaseCategory
    have hwordTranslatedWeight :
        pauliWeight (CollisionWord.toPauli word +
          CollisionWord.toPauli translation) = 3 := by
      rw [hwordTranslated]
      exact hmateWeight
    have hwordTranslatedCategory :
        0 < p03CategoryC (CollisionWord.toPauli word)
          (CollisionWord.toPauli word +
            CollisionWord.toPauli translation) := by
      rw [hwordTranslated]
      exact hwordCategory
    have hcross := p01_cross_weight_le_four
      (g := CollisionWord.toPauli baseWord)
      (h := CollisionWord.toPauli word)
      (u := CollisionWord.toPauli translation)
      hbaseTranslation.2 hbaseWordWeight
      hbaseTranslatedWeight hbaseTranslatedCategory
      hwordWeight
      hwordTranslatedWeight hwordTranslatedCategory
    rcases hcross with hlow | hlow
    · have hsemanticNe :
          CollisionWord.toPauli baseWord ≠ CollisionWord.toPauli word := by
        intro heq
        exact hwordBase (CollisionWord.pauliEquiv.injective heq).symm
      have hsum := p01_shadow_sum_mem_stabilizer_weight_four
        S hcandidate hA1 hA2 hA3 hbaseWordData.1 hwordData.1
          hsemanticNe hlow
      have hsumUnique := hunique
        (CollisionWord.toPauli baseWord + CollisionWord.toPauli word) hsum
      have hwordEqSemantic :
          CollisionWord.toPauli word = CollisionWord.toPauli baseMate := by
        apply add_left_cancel (a := CollisionWord.toPauli baseWord)
        calc
          CollisionWord.toPauli baseWord + CollisionWord.toPauli word =
              uniqueFour := hsumUnique
          _ = CollisionWord.toPauli translation := hbaseUnique.symm
          _ = CollisionWord.toPauli baseWord +
              CollisionWord.toPauli baseMate := by
            rw [show translation = CollisionWord.add baseWord baseMate by rfl,
              CollisionWord.toPauli_add]
      exact hwordMate (CollisionWord.pauliEquiv.injective hwordEqSemantic)
    · have hbaseNeCurrentMate : baseWord ≠ mate := by
        intro hmateBase
        subst mate
        have hwordEqSemantic :
            CollisionWord.toPauli word = CollisionWord.toPauli baseMate := by
          apply add_right_cancel (b := CollisionWord.toPauli baseWord)
          calc
            CollisionWord.toPauli word + CollisionWord.toPauli baseWord =
                CollisionWord.toPauli (CollisionWord.add word baseWord) := by
              rw [CollisionWord.toPauli_add]
            _ = CollisionWord.toPauli translation :=
              congrArg CollisionWord.toPauli htranslation
            _ = CollisionWord.toPauli baseWord +
                CollisionWord.toPauli baseMate := by
              rw [show translation = CollisionWord.add baseWord baseMate by rfl,
                CollisionWord.toPauli_add]
            _ = CollisionWord.toPauli baseMate +
                CollisionWord.toPauli baseWord := add_comm _ _
        exact hwordMate
          (CollisionWord.pauliEquiv.injective hwordEqSemantic)
      have hsemanticNe :
          CollisionWord.toPauli baseWord ≠ CollisionWord.toPauli mate := by
        intro heq
        exact hbaseNeCurrentMate (CollisionWord.pauliEquiv.injective heq)
      have hlow' :
          pauliWeight (CollisionWord.toPauli baseWord +
            CollisionWord.toPauli mate) ≤ 4 := by
        simpa [hwordTranslated] using hlow
      have hsum := p01_shadow_sum_mem_stabilizer_weight_four
        S hcandidate hA1 hA2 hA3 hbaseWordData.1 hmateData.1
          hsemanticNe hlow'
      have hsumUnique := hunique
        (CollisionWord.toPauli baseWord + CollisionWord.toPauli mate) hsum
      have hmateEqSemantic :
          CollisionWord.toPauli mate = CollisionWord.toPauli baseMate := by
        apply add_left_cancel (a := CollisionWord.toPauli baseWord)
        calc
          CollisionWord.toPauli baseWord + CollisionWord.toPauli mate =
              uniqueFour := hsumUnique
          _ = CollisionWord.toPauli translation := hbaseUnique.symm
          _ = CollisionWord.toPauli baseWord +
              CollisionWord.toPauli baseMate := by
            rw [show translation = CollisionWord.add baseWord baseMate by rfl,
              CollisionWord.toPauli_add]
      have hmateEq : mate = baseMate :=
        CollisionWord.pauliEquiv.injective hmateEqSemantic
      subst mate
      have hwordEqSemantic :
          CollisionWord.toPauli word = CollisionWord.toPauli baseWord := by
        apply add_right_cancel (b := CollisionWord.toPauli baseMate)
        calc
          CollisionWord.toPauli word + CollisionWord.toPauli baseMate =
              CollisionWord.toPauli (CollisionWord.add word baseMate) := by
            rw [CollisionWord.toPauli_add]
          _ = CollisionWord.toPauli translation :=
            congrArg CollisionWord.toPauli htranslation
          _ = CollisionWord.toPauli baseWord +
              CollisionWord.toPauli baseMate := by
            rw [show translation = CollisionWord.add baseWord baseMate by rfl,
              CollisionWord.toPauli_add]
      exact hwordBase
        (CollisionWord.pauliEquiv.injective hwordEqSemantic)
  have hcard := Finset.card_le_card hsubset
  have hpairNe : (baseWord, baseMate) ≠ (baseMate, baseWord) := by
    intro heq
    exact hbaseNe (congrArg Prod.fst heq)
  calc
    pairs.card ≤
        ({(baseWord, baseMate), (baseMate, baseWord)} :
          Finset (CollisionWord × CollisionWord)).card := hcard
    _ = 2 := Finset.card_pair hpairNe

end Quantum1435
