import Quantum1435.CollisionWordEquiv
import Quantum1435.P03IncidenceLower
import Quantum1435.P03ShadowVertices
import Mathlib.Tactic

/-!
# Actual shadow-word incidence in the p03 branch

This module instantiates the generic p03 incidence lower bound with the
literal finite set of weight-three shadow vectors.  A bin records a qubit
coordinate together with one of the three nonidentity phase-free Pauli
labels, so there are exactly `14 * 3 = 42` available bins.  A word is
incident with the injective image of its nonidentity support.

Under the semantic universal-row hypotheses for the p03 profile, the actual
shadow supplies twenty-four distinct computational words, each incident with
three bins.  The generic double-counting theorem therefore gives the lower
bound sixty for the ordered shared-bin occupancy sum.  No external list or
certificate is used in this construction.
-/

noncomputable section

namespace Quantum1435

/-- A coordinate/Pauli-label bin.  The finite set of available bins below
removes the identity label. -/
abbrev P03Bin := Fin 14 × LocalPauli

/-- The forty-two coordinate/nonidentity-label bins. -/
def p03AvailableBins : Finset P03Bin :=
  Finset.univ.filter fun bin ↦ bin.2 ≠ .I

/-- There are fourteen coordinates and three nonidentity labels. -/
theorem p03AvailableBins_card : p03AvailableBins.card = 42 := by
  decide

namespace CollisionWord

/-- The bins occupied by a computational word, obtained as the injective
image of its nonidentity support. -/
def wordBins (word : CollisionWord) : Finset P03Bin :=
  (Finset.univ.filter fun i ↦ word i ≠ .I).image fun i ↦ (i, word i)

@[simp] theorem mem_wordBins_iff (word : CollisionWord) (bin : P03Bin) :
    bin ∈ word.wordBins ↔ ∃ i : Fin 14, word i ≠ .I ∧ (i, word i) = bin := by
  simp [wordBins]

/-- Every occupied word bin is among the forty-two available bins. -/
theorem wordBins_subset_available (word : CollisionWord) :
    word.wordBins ⊆ p03AvailableBins := by
  intro bin hbin
  rcases (mem_wordBins_iff word bin).mp hbin with ⟨i, hi, rfl⟩
  simp [p03AvailableBins, hi]

/-- The coordinate component makes the support-to-bin map injective, hence
the number of occupied bins is exactly the Pauli weight. -/
@[simp] theorem card_wordBins (word : CollisionWord) :
    word.wordBins.card = word.weight := by
  let support : Finset (Fin 14) :=
    Finset.univ.filter fun i ↦ word i ≠ .I
  let supportBin : Fin 14 → P03Bin := fun i ↦ (i, word i)
  have hinjective : Function.Injective supportBin := by
    intro i j hij
    exact congrArg Prod.fst hij
  calc
    word.wordBins.card = (support.image supportBin).card := by
      rfl
    _ = support.card := Finset.card_image_of_injective support hinjective
    _ = word.weight := by rfl

end CollisionWord

/-- The actual weight-three shadow vectors, transported injectively into the
collision checker's computational representation. -/
noncomputable def p03ShadowCollisionWords
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    Finset CollisionWord :=
  (weightThreeShadowWords S hiso).image CollisionWord.ofPauli

theorem CollisionWord.ofPauli_injective :
    Function.Injective CollisionWord.ofPauli := by
  intro u v huv
  rw [← CollisionWord.toPauli_ofPauli u,
    ← CollisionWord.toPauli_ofPauli v, huv]

/-- Transport to the collision representation preserves the number of actual
shadow vertices. -/
theorem p03ShadowCollisionWords_card
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    (p03ShadowCollisionWords S hiso).card =
      (weightThreeShadowWords S hiso).card := by
  exact Finset.card_image_of_injective _ CollisionWord.ofPauli_injective

/-- Under the p03 profile and the two semantic universal rows, the transported
actual shadow set has exactly twenty-four vertices. -/
theorem p03ShadowCollisionWords_card_eq_24
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    (p03ShadowCollisionWords S hcandidate.2.1).card = 24 := by
  rw [p03ShadowCollisionWords_card]
  exact p03_weightThreeShadowWords_card_eq_24
    S hcandidate hodd hA2 hA4 hrows

/-- Every transported actual shadow vertex occupies exactly three bins. -/
theorem p03ShadowCollisionWords_card_wordBins
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (word : CollisionWord) (hword : word ∈ p03ShadowCollisionWords S hiso) :
    word.wordBins.card = 3 := by
  rcases Finset.mem_image.mp hword with ⟨v, hv, rfl⟩
  rw [CollisionWord.card_wordBins, CollisionWord.weight_ofPauli]
  exact (mem_weightThreeShadowWords S hiso v).mp hv |>.2

/-- Incidence means that a word occupies the given nonidentity
coordinate/label bin. -/
def p03WordIncident (word : CollisionWord) (bin : P03Bin) : Prop :=
  bin ∈ word.wordBins

instance : DecidableRel p03WordIncident := by
  intro word bin
  unfold p03WordIncident
  infer_instance

/-- The literal p03 shadow vertices force at least sixty ordered shared-bin
incidences.  This is the semantic lower bound before identifying those pairs
with collision-graph edges. -/
theorem p03Shadow_incidenceOccupancy_lower
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    60 ≤ ∑ bin ∈ p03AvailableBins,
      incidenceOccupancy
          (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin *
        (incidenceOccupancy
          (p03ShadowCollisionWords S hcandidate.2.1) p03WordIncident bin - 1) := by
  apply sixty_le_sum_incidenceOccupancy_mul_pred
  · exact p03ShadowCollisionWords_card_eq_24
      S hcandidate hodd hA2 hA4 hrows
  · exact p03AvailableBins_card
  · intro word hword
    have hfilter :
        (p03AvailableBins.filter fun bin ↦ p03WordIncident word bin) =
          word.wordBins := by
      ext bin
      constructor
      · intro hbin
        exact (Finset.mem_filter.mp hbin).2
      · intro hbin
        exact Finset.mem_filter.mpr
          ⟨CollisionWord.wordBins_subset_available word hbin, hbin⟩
    rw [hfilter]
    exact p03ShadowCollisionWords_card_wordBins
      S hcandidate.2.1 word hword

end Quantum1435
