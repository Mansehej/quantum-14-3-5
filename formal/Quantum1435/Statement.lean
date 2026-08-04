import Quantum1435.Normalizer
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The target theorem

This file fixes the exact proposition to be proved.  It is intentionally a
mathematical statement about subspaces, not a statement about serialized
certificates or the output of an external checker.
-/

namespace Quantum1435

/-- A putative binary `[[14,3]]` stabilizer with logical distance at least 5.

The dimension `11 = 14 - 3` expresses the three encoded logical qubits.  The
distance predicate quantifies over `Sᵖ \ S`, so low-weight elements of `S`
remain allowed: this includes degenerate stabilizer codes. -/
def IsCandidate1435 (S : Submodule F₂ (Pauli 14)) : Prop :=
  Module.finrank F₂ S = 11 ∧
    IsTotallyIsotropic S ∧
    HasLogicalDistanceAtLeast S 5

/-- The exact formal target of the development. -/
def NoBinaryStabilizer1435 : Prop :=
  ¬ ∃ S : Submodule F₂ (Pauli 14), IsCandidate1435 S

/-- Exact-distance-five candidates are included in the stronger lower-bound
formulation used by `NoBinaryStabilizer1435`. -/
theorem exactDistanceFive_isCandidate
    {S : Submodule F₂ (Pauli 14)}
    (hdim : Module.finrank F₂ S = 11)
    (hiso : IsTotallyIsotropic S)
    (hd : LogicalDistanceIs S 5) : IsCandidate1435 S :=
  ⟨hdim, hiso, hd.atLeast⟩

theorem IsCandidate1435.normalizer_finrank
    {S : Submodule F₂ (Pauli 14)} (h : IsCandidate1435 S) :
    Module.finrank F₂ (symplecticNormalizer S) = 17 :=
  finrank_normalizer_14_11 S h.1

theorem IsCandidate1435.le_normalizer
    {S : Submodule F₂ (Pauli 14)} (h : IsCandidate1435 S) :
    S ≤ symplecticNormalizer S :=
  h.2.1.le_normalizer

theorem IsCandidate1435.exists_logical
    {S : Submodule F₂ (Pauli 14)} (h : IsCandidate1435 S) :
    ∃ v, IsLogical S v := exists_logical_of_finrank_eleven S h.1

end Quantum1435
