import Quantum1435.P03InvariantBounds

/-!
# Representative-free rank-two collision bounds

This file proves the p2 collision bound directly from the coordinate
categories of an arbitrary rank-two plane. No coordinate permutation,
local Clifford normalization, or displayed representative is used.
-/

namespace Quantum1435

def p03CategoryAIndices (u v : CollisionWord) : Finset (Fin 14) :=
  Finset.univ.filter fun i ↦ u i ≠ .I ∧ v i = .I

def p03CategoryBIndices (u v : CollisionWord) : Finset (Fin 14) :=
  Finset.univ.filter fun i ↦ u i = .I ∧ v i ≠ .I

def p03CategoryCIndices (u v : CollisionWord) : Finset (Fin 14) :=
  Finset.univ.filter fun i ↦ u i ≠ .I ∧ u i = v i

theorem card_p03CategoryAIndices (u v : CollisionWord) :
    (p03CategoryAIndices u v).card =
      p03CategoryA (CollisionWord.toPauli u) (CollisionWord.toPauli v) := by
  unfold p03CategoryAIndices p03CategoryA CollisionWord.toPauli
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases u i <;> cases v i <;> decide

theorem card_p03CategoryBIndices (u v : CollisionWord) :
    (p03CategoryBIndices u v).card =
      p03CategoryB (CollisionWord.toPauli u) (CollisionWord.toPauli v) := by
  unfold p03CategoryBIndices p03CategoryB CollisionWord.toPauli
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases u i <;> cases v i <;> decide

theorem card_p03CategoryCIndices (u v : CollisionWord) :
    (p03CategoryCIndices u v).card =
      p03CategoryC (CollisionWord.toPauli u) (CollisionWord.toPauli v) := by
  unfold p03CategoryCIndices p03CategoryC CollisionWord.toPauli
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases u i <;> cases v i <;> decide

private theorem LocalPauli.right_eq_add_iff (a b : LocalPauli) :
    b = LocalPauli.add a b ↔ a = .I := by
  cases a <;> cases b <;> decide

/-- Two size-two matching supports inside a weight-three word must meet. -/
private theorem matchingSupport_inter_nonempty_of_collisions
    {word u v : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (hcu : IsCollision word u) (hcv : IsCollision word v) :
    (p03MatchingSupport word u ∩ p03MatchingSupport word v).Nonempty := by
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
  by_contra hempty
  have hdisjoint : Disjoint mu mv := by
    rw [Finset.disjoint_left]
    intro i hiu hiv
    exact hempty ⟨i, Finset.mem_inter.mpr ⟨hiu, hiv⟩⟩
  have hunionCard : (mu ∪ mv).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hmu, hmv]
  have hunionSubset : mu ∪ mv ⊆
      p03Support (CollisionWord.toPauli word) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiu | hiv
    · have hiu' := (Finset.mem_filter.mp hiu).2.1
      simpa [p03Support, CollisionWord.toPauli] using hiu'
    · have hiv' := (Finset.mem_filter.mp hiv).2.1
      simpa [p03Support, CollisionWord.toPauli] using hiv'
  have hle := Finset.card_le_card hunionSubset
  rw [hunionCard, card_p03Support_toPauli, hword] at hle
  omega

private theorem matchingSupport_u_add_subset_categoryA
    (word u v : CollisionWord) :
    p03MatchingSupport word u ∩
        p03MatchingSupport word (CollisionWord.add u v) ⊆
      p03CategoryAIndices u v := by
  intro i hi
  have hiu := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
  have hiw := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
  have huNonzero : u i ≠ .I := by
    intro huI
    exact hiu.1 (hiu.2.trans huI)
  have hvI : v i = .I :=
    (LocalPauli.left_eq_add_iff (u i) (v i)).mp
      (hiu.2.symm.trans hiw.2)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, ⟨huNonzero, hvI⟩⟩

private theorem matchingSupport_v_add_subset_categoryB
    (word u v : CollisionWord) :
    p03MatchingSupport word v ∩
        p03MatchingSupport word (CollisionWord.add u v) ⊆
      p03CategoryBIndices u v := by
  intro i hi
  have hiv := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
  have hiw := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
  have hvNonzero : v i ≠ .I := by
    intro hvI
    exact hiv.1 (hiv.2.trans hvI)
  have huI : u i = .I :=
    (LocalPauli.right_eq_add_iff (u i) (v i)).mp
      (hiv.2.symm.trans hiw.2)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, ⟨huI, hvNonzero⟩⟩

private theorem matchingSupport_uv_subset_categoryC
    (word u v : CollisionWord) :
    p03MatchingSupport word u ∩ p03MatchingSupport word v ⊆
      p03CategoryCIndices u v := by
  intro i hi
  have hiu := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
  have hiv := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
  have huNonzero : u i ≠ .I := by
    intro huI
    exact hiu.1 (hiu.2.trans huI)
  have huv : u i = v i := hiu.2.symm.trans hiv.2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, ⟨huNonzero, huv⟩⟩

def p03RankTwoExceptionalWord (u v : CollisionWord)
    (a b c : Fin 14) : CollisionWord :=
  fun i ↦
    if i = a then u a
    else if i = b then v b
    else if i = c then u c
    else .I

def p03RankTwoExceptionalWords (u v : CollisionWord) :
    Finset CollisionWord :=
  (((p03CategoryAIndices u v).product (p03CategoryBIndices u v)).product
    (p03CategoryCIndices u v)).image fun q ↦
      p03RankTwoExceptionalWord u v q.1.1 q.1.2 q.2

private theorem category_indices_pairwise_ne
    {u v : CollisionWord} {a b c : Fin 14}
    (ha : a ∈ p03CategoryAIndices u v)
    (hb : b ∈ p03CategoryBIndices u v)
    (hc : c ∈ p03CategoryCIndices u v) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  have hc' := (Finset.mem_filter.mp hc).2
  constructor
  · intro hab
    subst b
    exact ha'.1 hb'.1
  constructor
  · intro hac
    subst c
    exact hc'.1 (hc'.2.trans ha'.2)
  · intro hbc
    subst c
    exact hc'.1 hb'.1

private theorem word_eq_exceptional_of_matching_coordinates
    {word u v : CollisionWord} {a b c : Fin 14}
    (hword : CollisionWord.weight word = 3)
    (ha : a ∈ p03MatchingSupport word u ∩
      p03MatchingSupport word (CollisionWord.add u v))
    (hb : b ∈ p03MatchingSupport word v ∩
      p03MatchingSupport word (CollisionWord.add u v))
    (hc : c ∈ p03MatchingSupport word u ∩
      p03MatchingSupport word v)
    (haCategory : a ∈ p03CategoryAIndices u v)
    (hbCategory : b ∈ p03CategoryBIndices u v)
    (hcCategory : c ∈ p03CategoryCIndices u v) :
    word = p03RankTwoExceptionalWord u v a b c := by
  have hne := category_indices_pairwise_ne haCategory hbCategory hcCategory
  have haMatch := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
  have hbMatch := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2
  have hcMatch := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2
  have hsubset : ({a, b, c} : Finset (Fin 14)) ⊆
      p03Support (CollisionWord.toPauli word) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simpa [p03Support, CollisionWord.toPauli] using haMatch.1
    · simpa [p03Support, CollisionWord.toPauli] using hbMatch.1
    · simpa [p03Support, CollisionWord.toPauli] using hcMatch.1
  have htripleCard : ({a, b, c} : Finset (Fin 14)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr hne
  have hsupportCard :
      (p03Support (CollisionWord.toPauli word)).card = 3 := by
    rw [card_p03Support_toPauli, hword]
  have hsupport : ({a, b, c} : Finset (Fin 14)) =
      p03Support (CollisionWord.toPauli word) :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  funext i
  by_cases hia : i = a
  · subst i
    simp [p03RankTwoExceptionalWord, haMatch.2]
  by_cases hib : i = b
  · subst i
    simp [p03RankTwoExceptionalWord, hia, hbMatch.2]
  by_cases hic : i = c
  · subst i
    simp [p03RankTwoExceptionalWord, hia, hib, hcMatch.2]
  have hiI : word i = .I := by
    by_contra hiNonzero
    have hiSupport : i ∈ p03Support (CollisionWord.toPauli word) := by
      simpa [p03Support, CollisionWord.toPauli] using hiNonzero
    rw [← hsupport] at hiSupport
    simp [hia, hib, hic] at hiSupport
  simp [p03RankTwoExceptionalWord, hia, hib, hic, hiI]

/-- A degree-three word for an arbitrary rank-two triple belongs to the
coordinate-free `A × B × C` exceptional set. -/
theorem mem_p03RankTwoExceptionalWords_of_degree_three
    {word u v : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hdegree : 2 < collisionDegree word
      [u, v, CollisionWord.add u v]) :
    word ∈ p03RankTwoExceptionalWords u v := by
  have hcollisions :=
    (two_lt_collisionDegree_triple_iff
      word u v (CollisionWord.add u v)).mp hdegree
  obtain ⟨a, ha⟩ := matchingSupport_inter_nonempty_of_collisions
    hword hu huv hcollisions.1 hcollisions.2.2
  obtain ⟨b, hb⟩ := matchingSupport_inter_nonempty_of_collisions
    hword hv huv hcollisions.2.1 hcollisions.2.2
  obtain ⟨c, hc⟩ := matchingSupport_inter_nonempty_of_collisions
    hword hu hv hcollisions.1 hcollisions.2.1
  have haCategory := matchingSupport_u_add_subset_categoryA word u v ha
  have hbCategory := matchingSupport_v_add_subset_categoryB word u v hb
  have hcCategory := matchingSupport_uv_subset_categoryC word u v hc
  have hwordEq := word_eq_exceptional_of_matching_coordinates
    hword ha hb hc haCategory hbCategory hcCategory
  apply Finset.mem_image.mpr
  refine ⟨((a, b), c), ?_, hwordEq.symm⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨haCategory, hbCategory⟩, hcCategory⟩

theorem p03RankTwoExceptionalWords_card_le_eight
    (u v : CollisionWord)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2) :
    (p03RankTwoExceptionalWords u v).card ≤ 8 := by
  calc
    (p03RankTwoExceptionalWords u v).card ≤
        (((p03CategoryAIndices u v).product
          (p03CategoryBIndices u v)).product
          (p03CategoryCIndices u v)).card := Finset.card_image_le
    _ = (p03CategoryAIndices u v).card *
        (p03CategoryBIndices u v).card *
        (p03CategoryCIndices u v).card := by
      calc
        (((p03CategoryAIndices u v).product
            (p03CategoryBIndices u v)).product
            (p03CategoryCIndices u v)).card =
            ((p03CategoryAIndices u v).product
              (p03CategoryBIndices u v)).card *
              (p03CategoryCIndices u v).card :=
          Finset.card_product _ _
        _ = (p03CategoryAIndices u v).card *
            (p03CategoryBIndices u v).card *
            (p03CategoryCIndices u v).card := by
          exact congrArg
            (fun count ↦ count * (p03CategoryCIndices u v).card)
            (Finset.card_product
              (p03CategoryAIndices u v) (p03CategoryBIndices u v))
    _ = 8 := by
      rw [card_p03CategoryAIndices, card_p03CategoryBIndices,
        card_p03CategoryCIndices, hA, hB, hC]

theorem rankTwo_p2_selected_exception_card_le_eight
    {u v : CollisionWord} (selected : Finset CollisionWord)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2) :
    (selected.filter fun word ↦ 2 < collisionDegree word
      [u, v, CollisionWord.add u v]).card ≤ 8 := by
  have hsubset : selected.filter (fun word ↦ 2 < collisionDegree word
      [u, v, CollisionWord.add u v]) ⊆
      p03RankTwoExceptionalWords u v := by
    intro word hmem
    have hm := Finset.mem_filter.mp hmem
    exact mem_p03RankTwoExceptionalWords_of_degree_three
      (hword word hm.1) hu hv huv hm.2
  exact (Finset.card_le_card hsubset).trans
    (p03RankTwoExceptionalWords_card_le_eight u v hA hB hC)

/-- Representative-free p2 top-24 collision-degree bound. -/
theorem rankTwo_p2_selected_degree_sum_le_56
    {u v : CollisionWord} (selected : Finset CollisionWord)
    (hselected : selected.card ≤ 24)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2)
    (_hD : p03CategoryD (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 0) :
    (∑ word ∈ selected, collisionDegree word
      [u, v, CollisionWord.add u v]) ≤ 56 := by
  simpa using sum_le_of_selected_threshold
    (fun word : CollisionWord ↦ collisionDegree word
      [u, v, CollisionWord.add u v])
    2 3 8 24 (by decide) selected hselected
    (fun word _ ↦ collisionDegree_triple_le_three
      word u v (CollisionWord.add u v))
    (rankTwo_p2_selected_exception_card_le_eight selected hword
      hu hv huv hA hB hC)

/-! ## The invariant p1 exception -/

private theorem localPauli_add_eq_I_iff (a b : LocalPauli) :
    LocalPauli.add a b = .I ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem matchingSupport_eq_commonSupport_of_collision
    {word translation : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (htranslation : CollisionWord.weight translation = 4)
    (hcollision : IsCollision word translation) :
    p03MatchingSupport word translation =
      p03CommonSupport word translation := by
  have hsubset : p03MatchingSupport word translation ⊆
      p03CommonSupport word translation := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    change i ∈ p03Support (CollisionWord.toPauli word) ∩
      p03Support (CollisionWord.toPauli translation)
    rw [Finset.mem_inter]
    constructor
    · simpa [p03Support, CollisionWord.toPauli] using hi'.1
    · have htNonzero : translation i ≠ .I := by
        intro htI
        exact hi'.1 (hi'.2.trans htI)
      simpa [p03Support, CollisionWord.toPauli] using htNonzero
  have hmatching : (p03MatchingSupport word translation).card = 2 := by
    rw [← collisionMatchingCount_eq_card_matchingSupport]
    exact (isCollision_iff_overlap_two_and_matching_two
      word translation hword htranslation).mp hcollision |>.2
  have hcommon : (p03CommonSupport word translation).card = 2 :=
    card_commonSupport_eq_two_of_isCollision hword htranslation hcollision
  exact Finset.eq_of_subset_of_card_le hsubset (by omega)

private theorem translation_eq_I_of_not_mem_matching_of_collision
    {word translation : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (htranslation : CollisionWord.weight translation = 4)
    (hcollision : IsCollision word translation)
    {i : Fin 14} (hiWord : word i ≠ .I)
    (hiNotMatching : i ∉ p03MatchingSupport word translation) :
    translation i = .I := by
  have heq := matchingSupport_eq_commonSupport_of_collision
    hword htranslation hcollision
  by_contra hiTranslation
  have hiCommon : i ∈ p03CommonSupport word translation := by
    change i ∈ p03Support (CollisionWord.toPauli word) ∩
      p03Support (CollisionWord.toPauli translation)
    rw [Finset.mem_inter]
    constructor <;> simpa [p03Support, CollisionWord.toPauli]
  rw [← heq] at hiCommon
  exact hiNotMatching hiCommon

private theorem one_lt_collisionDegree_triple_iff
    (word a b c : CollisionWord) :
    1 < collisionDegree word [a, b, c] ↔
      (IsCollision word a ∧ IsCollision word b) ∨
      (IsCollision word a ∧ IsCollision word c) ∨
      (IsCollision word b ∧ IsCollision word c) := by
  by_cases ha : IsCollision word a <;>
    by_cases hb : IsCollision word b <;>
    by_cases hc : IsCollision word c <;>
    simp [collisionDegree, List.filter, ha, hb, hc]

private theorem isCollision_add_of_pair_of_matchingSupport_card_one
    {word a b : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (haWeight : CollisionWord.weight a = 4)
    (hbWeight : CollisionWord.weight b = 4)
    (hsumWeight : CollisionWord.weight (CollisionWord.add a b) = 4)
    (hshared : (p03MatchingSupport a b).card = 1)
    (hca : IsCollision word a) (hcb : IsCollision word b) :
    IsCollision word (CollisionWord.add a b) := by
  let ma := p03MatchingSupport word a
  let mb := p03MatchingSupport word b
  have hmaCard : ma.card = 2 := by
    rw [← collisionMatchingCount_eq_card_matchingSupport]
    exact (isCollision_iff_overlap_two_and_matching_two
      word a hword haWeight).mp hca |>.2
  have hmbCard : mb.card = 2 := by
    rw [← collisionMatchingCount_eq_card_matchingSupport]
    exact (isCollision_iff_overlap_two_and_matching_two
      word b hword hbWeight).mp hcb |>.2
  obtain ⟨c, hc⟩ := matchingSupport_inter_nonempty_of_collisions
    hword haWeight hbWeight hca hcb
  have hcMa : c ∈ ma := (Finset.mem_inter.mp hc).1
  have hcMb : c ∈ mb := (Finset.mem_inter.mp hc).2
  have hinterSubset : ma ∩ mb ⊆ p03MatchingSupport a b := by
    intro i hi
    have hia := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
    have hib := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
    have haNonzero : a i ≠ .I := by
      intro haI
      exact hia.1 (hia.2.trans haI)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, ⟨haNonzero, hia.2.symm.trans hib.2⟩⟩
  have hcShared : c ∈ p03MatchingSupport a b := hinterSubset hc
  have hsharedLe : (p03MatchingSupport a b).card ≤ 1 := hshared.le
  obtain ⟨x, hxMa, hxc⟩ := ma.exists_mem_ne (by omega) c
  have hxNotMb : x ∉ mb := by
    intro hxMb
    have hxShared := hinterSubset (Finset.mem_inter.mpr ⟨hxMa, hxMb⟩)
    exact hxc ((Finset.card_le_one.mp hsharedLe) x hxShared c hcShared)
  obtain ⟨y, hyMb, hyc⟩ := mb.exists_mem_ne (by omega) c
  have hyNotMa : y ∉ ma := by
    intro hyMa
    have hyShared := hinterSubset (Finset.mem_inter.mpr ⟨hyMa, hyMb⟩)
    exact hyc ((Finset.card_le_one.mp hsharedLe) y hyShared c hcShared)
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hxNotMb hyMb
  have hxData := (Finset.mem_filter.mp hxMa).2
  have hyData := (Finset.mem_filter.mp hyMb).2
  have hcAData := (Finset.mem_filter.mp hcMa).2
  have hcBData := (Finset.mem_filter.mp hcMb).2
  have hbXI : b x = .I :=
    translation_eq_I_of_not_mem_matching_of_collision
      hword hbWeight hcb hxData.1 hxNotMb
  have haYI : a y = .I :=
    translation_eq_I_of_not_mem_matching_of_collision
      hword haWeight hca hyData.1 hyNotMa
  have habC : a c = b c := hcAData.2.symm.trans hcBData.2
  have hxSum : word x = CollisionWord.add a b x := by
    change word x = LocalPauli.add (a x) (b x)
    calc
      word x = a x := hxData.2
      _ = LocalPauli.add (a x) (b x) := by
        rw [hbXI]
        cases a x <;> rfl
  have hySum : word y = CollisionWord.add a b y := by
    change word y = LocalPauli.add (a y) (b y)
    calc
      word y = b y := hyData.2
      _ = LocalPauli.add (a y) (b y) := by rw [haYI]; rfl
  have hcSumI : CollisionWord.add a b c = .I := by
    change LocalPauli.add (a c) (b c) = .I
    exact (localPauli_add_eq_I_iff (a c) (b c)).mpr habC
  have hsupportSubset : ({x, y, c} : Finset (Fin 14)) ⊆
      p03Support (CollisionWord.toPauli word) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simpa [p03Support, CollisionWord.toPauli] using hxData.1
    · simpa [p03Support, CollisionWord.toPauli] using hyData.1
    · simpa [p03Support, CollisionWord.toPauli] using hcAData.1
  have htripleCard : ({x, y, c} : Finset (Fin 14)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hxy, hxc, hyc⟩
  have hsupportCard :
      (p03Support (CollisionWord.toPauli word)).card = 3 := by
    rw [card_p03Support_toPauli, hword]
  have hsupport : ({x, y, c} : Finset (Fin 14)) =
      p03Support (CollisionWord.toPauli word) :=
    Finset.eq_of_subset_of_card_le hsupportSubset (by omega)
  have hmatchingSum : p03MatchingSupport word (CollisionWord.add a b) =
      {x, y} := by
    ext i
    simp only [p03MatchingSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hiNonzero, hiMatch⟩
      have hiSupport : i ∈ p03Support (CollisionWord.toPauli word) := by
        simpa [p03Support, CollisionWord.toPauli] using hiNonzero
      rw [← hsupport] at hiSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiSupport
      rcases hiSupport with hix | hiy | hic
      · exact Or.inl hix
      · exact Or.inr hiy
      · subst i
        exact False.elim (hiNonzero (hiMatch.trans hcSumI))
    · intro hi
      rcases hi with rfl | rfl
      · exact ⟨hxData.1, hxSum⟩
      · exact ⟨hyData.1, hySum⟩
  have hcommonSum : p03CommonSupport word (CollisionWord.add a b) =
      {x, y} := by
    ext i
    change (i ∈ p03Support (CollisionWord.toPauli word) ∩
      p03Support (CollisionWord.toPauli (CollisionWord.add a b))) ↔
      i ∈ ({x, y} : Finset (Fin 14))
    constructor
    · intro hi
      have hiWord := (Finset.mem_inter.mp hi).1
      have hiSum := (Finset.mem_inter.mp hi).2
      have hiSupport : i ∈ p03Support (CollisionWord.toPauli word) := hiWord
      rw [← hsupport] at hiSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiSupport
      rcases hiSupport with hix | hiy | hic
      · simp [hix]
      · simp [hiy]
      · subst i
        have : CollisionWord.add a b c ≠ .I := by
          simpa [p03Support, CollisionWord.toPauli] using hiSum
        exact False.elim (this hcSumI)
    · intro hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_inter]
      rcases hi with hix | hiy
      · constructor
        · subst i
          simpa [p03Support, CollisionWord.toPauli] using hxData.1
        · subst i
          have hxSumNonzero : CollisionWord.add a b x ≠ .I := by
            intro h
            exact hxData.1 (hxSum.trans h)
          simpa [p03Support, CollisionWord.toPauli] using hxSumNonzero
      · constructor
        · subst i
          simpa [p03Support, CollisionWord.toPauli] using hyData.1
        · subst i
          have hySumNonzero : CollisionWord.add a b y ≠ .I := by
            intro h
            exact hyData.1 (hySum.trans h)
          simpa [p03Support, CollisionWord.toPauli] using hySumNonzero
  apply (isCollision_iff_overlap_two_and_matching_two
    word (CollisionWord.add a b) hword hsumWeight).mpr
  constructor
  · rw [collisionOverlapCount_eq_card_commonSupport, hcommonSum]
    exact Finset.card_pair hxy
  · rw [collisionMatchingCount_eq_card_matchingSupport, hmatchingSum]
    exact Finset.card_pair hxy

private theorem collisionWord_add_left_self (u v : CollisionWord) :
    CollisionWord.add u (CollisionWord.add u v) = v := by
  funext i
  change LocalPauli.add (u i) (LocalPauli.add (u i) (v i)) = v i
  cases hu : u i <;> cases hv : v i <;> decide

private theorem collisionWord_add_right_self (u v : CollisionWord) :
    CollisionWord.add v (CollisionWord.add u v) = u := by
  funext i
  change LocalPauli.add (v i) (LocalPauli.add (u i) (v i)) = u i
  cases hu : u i <;> cases hv : v i <;> decide

private theorem rankTwo_p1_all_collisions_of_two
    {word u v : CollisionWord}
    (hword : CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hpairs :
      (IsCollision word u ∧ IsCollision word v) ∨
      (IsCollision word u ∧
        IsCollision word (CollisionWord.add u v)) ∨
      (IsCollision word v ∧
        IsCollision word (CollisionWord.add u v))) :
    IsCollision word u ∧ IsCollision word v ∧
      IsCollision word (CollisionWord.add u v) := by
  rcases hpairs with huvPair | huwPair | hvwPair
  · have hshared : (p03MatchingSupport u v).card = 1 := by
      rw [← collisionMatchingCount_eq_card_matchingSupport]
      exact hC
    exact ⟨huvPair.1, huvPair.2,
      isCollision_add_of_pair_of_matchingSupport_card_one
        hword hu hv huv hshared huvPair.1 huvPair.2⟩
  · have hshared :
        (p03MatchingSupport u (CollisionWord.add u v)).card = 1 := by
      rw [card_matchingSupport_self_add]
      exact hA
    have hthird := isCollision_add_of_pair_of_matchingSupport_card_one
      hword hu huv
        (by rw [collisionWord_add_left_self]; exact hv)
        hshared huwPair.1 huwPair.2
    rw [collisionWord_add_left_self] at hthird
    exact ⟨huwPair.1, hthird, huwPair.2⟩
  · have hshared :
        (p03MatchingSupport v (CollisionWord.add u v)).card = 1 := by
      rw [card_matchingSupport_right_add]
      exact hB
    have hthird := isCollision_add_of_pair_of_matchingSupport_card_one
      hword hv huv
        (by rw [collisionWord_add_right_self]; exact hu)
        hshared hvwPair.1 hvwPair.2
    rw [collisionWord_add_right_self] at hthird
    exact ⟨hthird, hvwPair.1, hvwPair.2⟩

theorem rankTwo_p1_selected_exception_card_le_one
    {u v : CollisionWord} (selected : Finset CollisionWord)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1) :
    (selected.filter fun word ↦ 1 < collisionDegree word
      [u, v, CollisionWord.add u v]).card ≤ 1 := by
  have hsubset : selected.filter (fun word ↦ 1 < collisionDegree word
      [u, v, CollisionWord.add u v]) ⊆
      p03RankTwoExceptionalWords u v := by
    intro word hmem
    have hm := Finset.mem_filter.mp hmem
    have hpairs := (one_lt_collisionDegree_triple_iff
      word u v (CollisionWord.add u v)).mp hm.2
    have hall := rankTwo_p1_all_collisions_of_two
      (hword word hm.1) hu hv huv hA hB hC hpairs
    apply mem_p03RankTwoExceptionalWords_of_degree_three
      (hword word hm.1) hu hv huv
    exact (two_lt_collisionDegree_triple_iff
      word u v (CollisionWord.add u v)).mpr hall
  calc
    (selected.filter fun word ↦ 1 < collisionDegree word
        [u, v, CollisionWord.add u v]).card ≤
      (p03RankTwoExceptionalWords u v).card := Finset.card_le_card hsubset
    _ ≤ (((p03CategoryAIndices u v).product
          (p03CategoryBIndices u v)).product
          (p03CategoryCIndices u v)).card := Finset.card_image_le
    _ = (p03CategoryAIndices u v).card *
        (p03CategoryBIndices u v).card *
        (p03CategoryCIndices u v).card := by
      calc
        (((p03CategoryAIndices u v).product
            (p03CategoryBIndices u v)).product
            (p03CategoryCIndices u v)).card =
            ((p03CategoryAIndices u v).product
              (p03CategoryBIndices u v)).card *
              (p03CategoryCIndices u v).card := Finset.card_product _ _
        _ = _ := by
          exact congrArg
            (fun count ↦ count * (p03CategoryCIndices u v).card)
            (Finset.card_product
              (p03CategoryAIndices u v) (p03CategoryBIndices u v))
    _ = 1 := by
      rw [card_p03CategoryAIndices, card_p03CategoryBIndices,
        card_p03CategoryCIndices, hA, hB, hC]

/-- Representative-free p1 top-24 collision-degree bound. -/
theorem rankTwo_p1_selected_degree_sum_le_26
    {u v : CollisionWord} (selected : Finset CollisionWord)
    (hselected : selected.card ≤ 24)
    (hword : ∀ word ∈ selected, CollisionWord.weight word = 3)
    (hu : CollisionWord.weight u = 4)
    (hv : CollisionWord.weight v = 4)
    (huv : CollisionWord.weight (CollisionWord.add u v) = 4)
    (hA : p03CategoryA (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hB : p03CategoryB (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (hC : p03CategoryC (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 1)
    (_hD : p03CategoryD (CollisionWord.toPauli u)
      (CollisionWord.toPauli v) = 2) :
    (∑ word ∈ selected, collisionDegree word
      [u, v, CollisionWord.add u v]) ≤ 26 := by
  simpa using sum_le_of_selected_threshold
    (fun word : CollisionWord ↦ collisionDegree word
      [u, v, CollisionWord.add u v])
    1 3 1 24 (by decide) selected hselected
    (fun word _ ↦ collisionDegree_triple_le_three
      word u v (CollisionWord.add u v))
    (rankTwo_p1_selected_exception_card_le_one selected hword
      hu hv huv hA hB hC)

end Quantum1435
