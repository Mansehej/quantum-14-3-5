import Quantum1435.EvenBranch
import Mathlib.Tactic

/-!
# A proved-sound linear certificate checker

This is the first executable Lean certificate path in the development.  A
generator may propose equations, multipliers, and a target equation, but the
Boolean checker recomputes their linear combination.  The soundness theorem
below is independent of the generator.
-/

namespace Quantum1435

structure LinearEquation (n : ℕ) where
  coeff : Fin n → ℤ
  rhs : ℤ

theorem LinearEquation.ext' {n : ℕ} {e f : LinearEquation n}
    (hcoeff : e.coeff = f.coeff) (hrhs : e.rhs = f.rhs) : e = f := by
  cases e
  cases f
  simp only at hcoeff hrhs
  cases hcoeff
  cases hrhs
  rfl

def LinearEquation.Holds {n : ℕ} (e : LinearEquation n) (x : Fin n → ℤ) : Prop :=
  (∑ i, e.coeff i * x i) = e.rhs

def linearCombination {m n : ℕ} (eqs : Fin m → LinearEquation n)
    (multipliers : Fin m → ℤ) : LinearEquation n where
  coeff i := ∑ j, multipliers j * (eqs j).coeff i
  rhs := ∑ j, multipliers j * (eqs j).rhs

/-- Every linear combination of valid source equations is valid. -/
theorem LinearEquation.holds_linearCombination {m n : ℕ}
    (eqs : Fin m → LinearEquation n) (multipliers : Fin m → ℤ)
    (x : Fin n → ℤ) (h : ∀ j, (eqs j).Holds x) :
    (linearCombination eqs multipliers).Holds x := by
  simp only [LinearEquation.Holds, linearCombination]
  calc
    ∑ i, (∑ j, multipliers j * (eqs j).coeff i) * x i =
        ∑ j, multipliers j * (∑ i, (eqs j).coeff i * x i) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1
          funext j
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j, multipliers j * (eqs j).rhs := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h j]

/-- Executable checker for an integer linear-combination certificate. -/
def checkLinearCombination {m n : ℕ} (eqs : Fin m → LinearEquation n)
    (multipliers : Fin m → ℤ) (target : LinearEquation n) : Bool :=
  decide ((linearCombination eqs multipliers).rhs = target.rhs) &&
    (List.finRange n).all fun i ↦
      decide ((linearCombination eqs multipliers).coeff i = target.coeff i)

/-- A `true` checker result implies equality with the claimed target. -/
theorem checkLinearCombination_sound {m n : ℕ}
    (eqs : Fin m → LinearEquation n) (multipliers : Fin m → ℤ)
    (target : LinearEquation n)
    (hcheck : checkLinearCombination eqs multipliers target = true) :
    linearCombination eqs multipliers = target := by
  have hand :
      decide ((linearCombination eqs multipliers).rhs = target.rhs) = true ∧
      (List.finRange n).all (fun i ↦
        decide ((linearCombination eqs multipliers).coeff i = target.coeff i)) = true := by
    simpa only [checkLinearCombination, Bool.and_eq_true] using hcheck
  have hrhs : (linearCombination eqs multipliers).rhs = target.rhs :=
    of_decide_eq_true hand.1
  have hcoeff : (linearCombination eqs multipliers).coeff = target.coeff := by
    funext i
    apply of_decide_eq_true
    exact (List.all_eq_true.mp hand.2) i (List.mem_finRange i)
  exact LinearEquation.ext' hcoeff hrhs

/-- The cardinality row after moving `A₀ = 1` to the right. -/
def evenTotalEquation : LinearEquation 7 :=
  ⟨![1, 1, 1, 1, 1, 1, 1], 2047⟩

/-- A distance/MacWilliams row generated from the Lean Krawtchouk function,
not from hardcoded transcript coefficients. -/
def evenKrawtchoukEquation (j : ℕ) : LinearEquation 7 where
  coeff i := evenDistanceCoefficient j (2 * (i.1 + 1))
  rhs := -quantumKrawtchouk 14 j 0

/-- The five all-even source rows, ordered by
`(A₂,A₄,A₆,A₈,A₁₀,A₁₂,A₁₄)`. -/
def evenEquations : Fin 5 → LinearEquation 7 := ![
  evenTotalEquation,
  evenKrawtchoukEquation 1,
  evenKrawtchoukEquation 2,
  evenKrawtchoukEquation 3,
  evenKrawtchoukEquation 4
]

def evenMultipliers : Fin 5 → ℤ := ![77, 38, 14, 5, 1]

def evenTarget : LinearEquation 7 :=
  ⟨![32768, 18432, 4096, 0, 0, 0, 0], 14336⟩

def checkEvenCertificate : Bool :=
  checkLinearCombination evenEquations evenMultipliers evenTarget

/-- Ordinary kernel reduction accepts the concrete certificate without a
compiler-evaluation shortcut. -/
theorem checkEvenCertificate_passes : checkEvenCertificate = true := by
  decide

/-- Sound end-to-end use of the accepted certificate on arbitrary integer
values satisfying the five source rows. -/
theorem checkEvenCertificate_sound (x : Fin 7 → ℤ)
    (h : ∀ j, (evenEquations j).Holds x) : evenTarget.Holds x := by
  have hc := LinearEquation.holds_linearCombination evenEquations evenMultipliers x h
  have heq := checkLinearCombination_sound evenEquations evenMultipliers evenTarget
    checkEvenCertificate_passes
  simpa [heq] using hc

/-- No nonnegative enumerator can satisfy all five checked source rows. -/
theorem noEvenEnumerator (A : Fin 7 → ℕ)
    (h : ∀ j, (evenEquations j).Holds (fun i ↦ (A i : ℤ))) : False := by
  have ht := checkEvenCertificate_sound (fun i ↦ (A i : ℤ)) h
  have hrel :
      32768 * (A 0 : ℤ) + (18432 * (A 1 : ℤ) + 4096 * (A 2 : ℤ)) =
        14336 := by
    simpa [LinearEquation.Holds, evenTarget, Fin.sum_univ_succ] using ht
  omega

end Quantum1435
