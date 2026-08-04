import Quantum1435.P03CollisionChecker
import Mathlib.Tactic

/-!
# Equivalence of computational and semantic Pauli words

The collision checker uses a four-element inductive type for one-qubit
Paulis, while the mathematical development uses `F₂ × F₂`.  This file
gives an explicit coordinatewise equivalence between those representations.
It allows later shadow-incidence arguments to move actual Pauli vectors into
the computational collision layer without trusting an external encoding.
-/

namespace Quantum1435

namespace LocalPauli

/-- Decode an `(X,Z)` bit pair as a phase-free one-qubit Pauli. -/
def ofBits (p : F₂ × F₂) : LocalPauli :=
  if p = (0, 0) then .I
  else if p = (1, 0) then .X
  else if p = (0, 1) then .Z
  else .Y

@[simp] theorem toBits_ofBits (p : F₂ × F₂) :
    (ofBits p).toBits = p := by
  rcases p with ⟨x, z⟩
  fin_cases x <;> fin_cases z <;> decide

@[simp] theorem ofBits_toBits (p : LocalPauli) :
    ofBits p.toBits = p := by
  cases p <;> decide

/-- The exact one-coordinate equivalence used by the collision checker. -/
def bitsEquiv : LocalPauli ≃ F₂ × F₂ where
  toFun := toBits
  invFun := ofBits
  left_inv := ofBits_toBits
  right_inv := toBits_ofBits

end LocalPauli

namespace CollisionWord

/-- Decode a mathematical Pauli vector into the checker's representation. -/
def ofPauli (v : Pauli 14) : CollisionWord :=
  fun i ↦ LocalPauli.ofBits (v i)

@[simp] theorem toPauli_ofPauli (v : Pauli 14) :
    toPauli (ofPauli v) = v := by
  funext i
  exact LocalPauli.toBits_ofBits (v i)

@[simp] theorem ofPauli_toPauli (w : CollisionWord) :
    ofPauli (toPauli w) = w := by
  funext i
  exact LocalPauli.ofBits_toBits (w i)

/-- Coordinatewise equivalence between all computational and semantic
fourteen-qubit Pauli words. -/
def pauliEquiv : CollisionWord ≃ Pauli 14 where
  toFun := toPauli
  invFun := ofPauli
  left_inv := ofPauli_toPauli
  right_inv := toPauli_ofPauli

@[simp] theorem weight_ofPauli (v : Pauli 14) :
    weight (ofPauli v) = pauliWeight v := by
  rw [weight_eq_pauliWeight, toPauli_ofPauli]

@[simp] theorem ofPauli_add (u v : Pauli 14) :
    ofPauli (u + v) = add (ofPauli u) (ofPauli v) := by
  calc
    ofPauli (u + v) =
        ofPauli (toPauli (add (ofPauli u) (ofPauli v))) := by
      congr 1
      rw [toPauli_add, toPauli_ofPauli, toPauli_ofPauli]
    _ = add (ofPauli u) (ofPauli v) := ofPauli_toPauli _

end CollisionWord

end Quantum1435
