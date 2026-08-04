import Quantum1435.OddArithmetic

/-!
# p03 collision-checker infrastructure

This module formalizes the four explicit normal-form Pauli triples, the
canonical weight-three parameter space, and finite certificate checkers.  It
does not read or trust the generated JSON certificate.

The generic threshold checker has a proved soundness theorem: an accepted
maximum-degree/exception-count certificate bounds every selected degree sum,
and a handshake hypothesis then bounds collision edges.  A second checker
ranges over the six finite support/label coordinates directly.

No theorem in this module currently asserts that a proposed p03 collision
certificate is accepted.  Ordinary kernel reduction of the full 9,828-case
certificate exceeded the feasibility-spike resource budget, so the proposed
tables below remain explicitly unaccepted data. The final nonexistence
theorem does not depend on those tables: invariant analytic bounds replace
them in `P03SemanticElimination`.
-/

namespace Quantum1435

/-- The four phase-free one-qubit Pauli labels. -/
inductive LocalPauli
  | I
  | X
  | Z
  | Y
  deriving DecidableEq, Repr, Fintype

namespace LocalPauli

/-- Phase-free Pauli multiplication, encoded as bitwise addition in `F₂²`. -/
def add : LocalPauli → LocalPauli → LocalPauli
  | .I, b => b
  | a, .I => a
  | .X, .X => .I
  | .X, .Z => .Y
  | .X, .Y => .Z
  | .Z, .X => .Y
  | .Z, .Z => .I
  | .Z, .Y => .X
  | .Y, .X => .Z
  | .Y, .Z => .X
  | .Y, .Y => .I

/-- The `(X,Z)` bit encoding used by `Pauli`. -/
def toBits : LocalPauli → F₂ × F₂
  | .I => (0, 0)
  | .X => (1, 0)
  | .Z => (0, 1)
  | .Y => (1, 1)

@[simp] theorem toBits_add (a b : LocalPauli) :
    toBits (add a b) = toBits a + toBits b := by
  cases a <;> cases b <;> decide

@[simp] theorem toBits_eq_zero_iff (a : LocalPauli) :
    toBits a = 0 ↔ a = .I := by
  cases a <;> decide

@[simp] theorem toBits_ne_zero_iff (a : LocalPauli) :
    toBits a ≠ 0 ↔ a ≠ .I := by
  cases a <;> decide

end LocalPauli

/-- A computational Pauli word on fourteen coordinates. -/
abbrev CollisionWord := Fin 14 → LocalPauli

namespace CollisionWord

/-- Interpret a computational word in the mathematical Pauli space. -/
def toPauli (w : CollisionWord) : Pauli 14 := fun i => (w i).toBits

/-- Coordinatewise phase-free Pauli multiplication. -/
def add (u v : CollisionWord) : CollisionWord := fun i => LocalPauli.add (u i) (v i)

/-- Hamming/Pauli weight of the computational representation. -/
def weight (w : CollisionWord) : ℕ :=
  (Finset.univ.filter fun i => w i ≠ .I).card

/-- Build an explicit fourteen-coordinate word from a label list. -/
def ofList (labels : List LocalPauli) : CollisionWord :=
  fun i => labels.getD i.val .I

@[simp] theorem toPauli_add (u v : CollisionWord) :
    toPauli (add u v) = toPauli u + toPauli v := by
  funext i
  simp [toPauli, add]

theorem weight_eq_pauliWeight (w : CollisionWord) :
    weight w = pauliWeight (toPauli w) := by
  apply congrArg Finset.card
  ext i
  simp [toPauli]

end CollisionWord

/-- Boolean test that two words share a nonzero coordinate/Pauli bin. -/
def sharesBin (word mate : CollisionWord) : Bool :=
  (List.ofFn fun i : Fin 14 => decide (word i ≠ .I ∧ word i = mate i)).any id

/-- Boolean collision test used by the finite checker. -/
def collisionTest (word translation : CollisionWord) : Bool :=
  decide (CollisionWord.weight (CollisionWord.add word translation) = 3) &&
    sharesBin word (CollisionWord.add word translation)

/-- A collision is a successful finite collision test. -/
def IsCollision (word translation : CollisionWord) : Prop :=
  collisionTest word translation = true

instance (word translation : CollisionWord) : Decidable (IsCollision word translation) :=
  by
    unfold IsCollision
    infer_instance

/-- Number of the listed translations that collide with a word. -/
def collisionDegree (word : CollisionWord) (translations : List CollisionWord) : ℕ :=
  (translations.filter fun t => IsCollision word t).length

/-- A computational collision is exactly the corresponding condition on the
mathematical phase-free Pauli sum, together with the same shared-bin witness. -/
theorem isCollision_iff_pauli (word translation : CollisionWord) :
    IsCollision word translation ↔
      pauliWeight (CollisionWord.toPauli word + CollisionWord.toPauli translation) = 3 ∧
        sharesBin word (CollisionWord.add word translation) = true := by
  simp only [IsCollision, collisionTest, Bool.and_eq_true, decide_eq_true_eq]
  rw [← CollisionWord.toPauli_add, ← CollisionWord.weight_eq_pauliWeight]

/-! ## The finite universe of weight-three words -/

structure SupportTriple where
  first : Fin 14
  second : Fin 14
  third : Fin 14
  deriving DecidableEq, Repr, Fintype

structure NonzeroLabelTriple where
  first : Fin 3
  second : Fin 3
  third : Fin 3
  deriving DecidableEq, Repr, Fintype

structure RawWeightThreeParameter where
  support : SupportTriple
  labels : NonzeroLabelTriple
  deriving DecidableEq, Repr, Fintype

/-- Canonical weight-three parameters have a strictly increasing support. -/
abbrev WeightThreeParameter :=
  {p : RawWeightThreeParameter // p.support.first < p.support.second ∧
    p.support.second < p.support.third}

/-- Decode `Fin 3` as X, Z, Y (the three nonidentity labels). -/
def nonzeroLabel (a : Fin 3) : LocalPauli :=
  if a.val = 0 then .X else if a.val = 1 then .Z else .Y

/-- Decode a canonical parameter as a fourteen-coordinate Pauli word. -/
def WeightThreeParameter.word (p : WeightThreeParameter) : CollisionWord :=
  fun i =>
    if i = p.1.support.first then nonzeroLabel p.1.labels.first
    else if i = p.1.support.second then nonzeroLabel p.1.labels.second
    else if i = p.1.support.third then nonzeroLabel p.1.labels.third
    else .I

/-- The sorted-support parameter count is arithmetically
`choose(14,3) * 3^3 = 9828`. -/
theorem weightThreeParameter_count_formula :
    Nat.choose 14 3 * 3 ^ 3 = 9828 := by
  decide

/-! ## Explicit p03 normal forms -/

private def explicitWord (labels : List LocalPauli) : CollisionWord :=
  CollisionWord.ofList labels

def rankThreeGenerators : List CollisionWord :=
  [ explicitWord [.X, .X, .X, .X, .I, .I, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.I, .I, .I, .I, .X, .X, .X, .X, .I, .I, .I, .I, .I, .I],
    explicitWord [.I, .I, .I, .I, .I, .I, .I, .I, .X, .X, .X, .X, .I, .I] ]

def rankTwo0Generators : List CollisionWord :=
  [ explicitWord [.X, .X, .X, .X, .I, .I, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.Z, .Z, .Z, .Z, .I, .I, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.Y, .Y, .Y, .Y, .I, .I, .I, .I, .I, .I, .I, .I, .I, .I] ]

def rankTwo1Generators : List CollisionWord :=
  [ explicitWord [.X, .I, .X, .X, .X, .I, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.I, .X, .X, .Z, .Z, .I, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.X, .X, .I, .Y, .Y, .I, .I, .I, .I, .I, .I, .I, .I, .I] ]

def rankTwo2Generators : List CollisionWord :=
  [ explicitWord [.X, .X, .I, .I, .X, .X, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.I, .I, .X, .X, .X, .X, .I, .I, .I, .I, .I, .I, .I, .I],
    explicitWord [.X, .X, .X, .X, .I, .I, .I, .I, .I, .I, .I, .I, .I, .I] ]

def p03NormalFormGenerators : P03NormalForm → List CollisionWord
  | .rankTwo0 => rankTwo0Generators
  | .rankTwo1 => rankTwo1Generators
  | .rankTwo2 => rankTwo2Generators
  | .rankThree => rankThreeGenerators

/-- The explicit lists really are triples of commuting weight-four Paulis. -/
def NormalFormGeneratorsWellFormed (translations : List CollisionWord) : Prop :=
  translations.length = 3 ∧
    translations.all (fun t => decide (CollisionWord.weight t = 4)) = true ∧
    translations.all (fun u =>
      translations.all (fun v =>
        decide (symplecticForm 14 (CollisionWord.toPauli u)
          (CollisionWord.toPauli v) = 0))) = true

instance (translations : List CollisionWord) :
    Decidable (NormalFormGeneratorsWellFormed translations) := by
  unfold NormalFormGeneratorsWellFormed
  infer_instance

set_option maxRecDepth 100000 in
theorem p03NormalFormGenerators_wellFormed (form : P03NormalForm) :
    NormalFormGeneratorsWellFormed (p03NormalFormGenerators form) := by
  cases form <;> decide

/-! ## A generic, proved-sound threshold checker -/

/-- The semantic facts checked by a threshold certificate. -/
def ThresholdBound {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℕ) (base maximum exceptionalCap : ℕ) : Prop :=
  base ≤ maximum ∧
    (Finset.univ.filter fun x => maximum < score x).card = 0 ∧
    (Finset.univ.filter fun x => base < score x).card ≤ exceptionalCap

instance {α : Type*} [Fintype α] [DecidableEq α] (score : α → ℕ)
    (base maximum exceptionalCap : ℕ) :
    Decidable (ThresholdBound score base maximum exceptionalCap) := by
  unfold ThresholdBound
  infer_instance

/-- A finite Boolean checker for `ThresholdBound`. -/
def checkThresholdBound {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℕ) (base maximum exceptionalCap : ℕ) : Bool :=
  decide (ThresholdBound score base maximum exceptionalCap)

/-- The Boolean threshold checker is sound; the generator of a proposed
certificate is outside the trusted base. -/
theorem checkThresholdBound_sound {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℕ) (base maximum exceptionalCap : ℕ)
    (h : checkThresholdBound score base maximum exceptionalCap = true) :
    ThresholdBound score base maximum exceptionalCap := by
  exact of_decide_eq_true (by simpa [checkThresholdBound] using h)

/-- A constant indicator sum is the constant times the filtered cardinality. -/
theorem sum_ite_const_eq_mul_card_filter {α : Type*} [DecidableEq α]
    (selected : Finset α) (predicate : α → Prop) [DecidablePred predicate]
    (constant : ℕ) :
    (∑ x ∈ selected, if predicate x then constant else 0) =
      constant * (selected.filter predicate).card := by
  calc
    (∑ x ∈ selected, if predicate x then constant else 0) =
        constant * ∑ x ∈ selected, if predicate x then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hp : predicate x <;> simp [hp]
    _ = constant * (selected.filter predicate).card := by
      rw [Finset.sum_boole]
      simp

/-- A checked threshold bound controls the total score of every selected
finite set. -/
theorem sum_le_of_thresholdBound {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℕ) (base maximum exceptionalCap selectedCap : ℕ)
    (h : ThresholdBound score base maximum exceptionalCap)
    (selected : Finset α) (hselected : selected.card ≤ selectedCap) :
    (∑ x ∈ selected, score x) ≤
      base * selectedCap + (maximum - base) * exceptionalCap := by
  let exceptional := selected.filter fun x => base < score x
  have hexceptional_subset :
      exceptional ⊆ Finset.univ.filter fun x => base < score x := by
    intro x hx
    simp only [exceptional, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ x, hx.2⟩
  have hexceptional_card : exceptional.card ≤ exceptionalCap :=
    (Finset.card_le_card hexceptional_subset).trans h.2.2
  have hpoint : ∀ x ∈ selected,
      score x ≤ base + (maximum - base) * if base < score x then 1 else 0 := by
    intro x hx
    by_cases hhigh : base < score x
    · simp only [hhigh, if_true, mul_one]
      have hempty :
          (Finset.univ.filter fun x => maximum < score x) = ∅ :=
        Finset.card_eq_zero.mp h.2.1
      have hxmax : score x ≤ maximum := by
        have hnotmem : x ∉ (Finset.univ.filter fun x => maximum < score x) := by
          rw [hempty]
          simp
        simpa using hnotmem
      omega
    · simp only [hhigh, if_false, mul_zero, add_zero]
      omega
  calc
    (∑ x ∈ selected, score x) ≤
        ∑ x ∈ selected,
          (base + (maximum - base) * if base < score x then 1 else 0) :=
      Finset.sum_le_sum hpoint
    _ = base * selected.card + (maximum - base) * exceptional.card := by
      have hindicator := sum_ite_const_eq_mul_card_filter selected
        (fun x => base < score x) (maximum - base)
      rw [Finset.sum_add_distrib]
      have hindicator' :
          (∑ x ∈ selected, if base < score x then maximum - base else 0) =
            (maximum - base) * exceptional.card := by
        simpa [exceptional] using hindicator
      simp only [mul_ite, mul_one, mul_zero]
      rw [hindicator']
      simp [mul_comm]
    _ ≤ base * selectedCap + (maximum - base) * exceptionalCap :=
      Nat.add_le_add (Nat.mul_le_mul_left base hselected)
        (Nat.mul_le_mul_left (maximum - base) hexceptional_card)

/-- Exact degree counts and the threshold data carried by a finite
certificate. -/
structure CollisionCertificate where
  degree0 : ℕ
  degree1 : ℕ
  degree2 : ℕ
  degree3 : ℕ
  baseDegree : ℕ
  maximumDegree : ℕ
  exceptionalCap : ℕ
  selectedCap : ℕ
  degreeSumBound : ℕ
  edgeUpperBound : ℕ
  deriving DecidableEq, Repr

def countDegree {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℕ) (degree : ℕ) : ℕ :=
  (Finset.univ.filter fun x => score x = degree).card

/-- Full semantic validity of a collision certificate. -/
def CollisionCertificate.Valid {α : Type*} [Fintype α] [DecidableEq α]
    (certificate : CollisionCertificate) (score : α → ℕ) : Prop :=
  countDegree score 0 = certificate.degree0 ∧
    countDegree score 1 = certificate.degree1 ∧
    countDegree score 2 = certificate.degree2 ∧
    countDegree score 3 = certificate.degree3 ∧
    certificate.degree0 + certificate.degree1 + certificate.degree2 +
        certificate.degree3 = Fintype.card α ∧
    ThresholdBound score certificate.baseDegree certificate.maximumDegree
      certificate.exceptionalCap ∧
    certificate.degreeSumBound =
      certificate.baseDegree * certificate.selectedCap +
        (certificate.maximumDegree - certificate.baseDegree) *
          certificate.exceptionalCap ∧
    certificate.edgeUpperBound = certificate.degreeSumBound / 2

instance {α : Type*} [Fintype α] [DecidableEq α]
    (certificate : CollisionCertificate) (score : α → ℕ) :
    Decidable (certificate.Valid score) := by
  unfold CollisionCertificate.Valid
  infer_instance

/-- The generic finite collision-certificate checker. -/
def checkCollisionCertificate {α : Type*} [Fintype α] [DecidableEq α]
    (certificate : CollisionCertificate) (score : α → ℕ) : Bool :=
  decide (certificate.Valid score)

theorem checkCollisionCertificate_valid {α : Type*} [Fintype α] [DecidableEq α]
    (certificate : CollisionCertificate) (score : α → ℕ)
    (h : checkCollisionCertificate certificate score = true) :
    certificate.Valid score := by
  exact of_decide_eq_true (by simpa [checkCollisionCertificate] using h)

/-- Soundness of the checked top-`k` degree-sum bound. -/
theorem checkCollisionCertificate_sum_sound
    {α : Type*} [Fintype α] [DecidableEq α]
    (certificate : CollisionCertificate) (score : α → ℕ)
    (h : checkCollisionCertificate certificate score = true)
    (selected : Finset α) (hselected : selected.card ≤ certificate.selectedCap) :
    (∑ x ∈ selected, score x) ≤ certificate.degreeSumBound := by
  have hv := checkCollisionCertificate_valid certificate score h
  rcases hv with ⟨_, _, _, _, _, hthreshold, hsum, _⟩
  rw [hsum]
  exact sum_le_of_thresholdBound score certificate.baseDegree
    certificate.maximumDegree certificate.exceptionalCap certificate.selectedCap
    hthreshold selected hselected

/-- Soundness of the collision-edge upper bound, conditional only on the
usual handshake inequality for the selected collision graph. -/
theorem checkCollisionCertificate_edges_sound
    {α : Type*} [Fintype α] [DecidableEq α]
    (certificate : CollisionCertificate) (score : α → ℕ)
    (h : checkCollisionCertificate certificate score = true)
    (selected : Finset α) (hselected : selected.card ≤ certificate.selectedCap)
    (edges : ℕ) (handshake : 2 * edges ≤ ∑ x ∈ selected, score x) :
    edges ≤ certificate.edgeUpperBound := by
  have hv := checkCollisionCertificate_valid certificate score h
  rcases hv with ⟨_, _, _, _, _, _, _, hedge⟩
  rw [hedge]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  simpa [mul_comm] using
    handshake.trans (checkCollisionCertificate_sum_sound certificate score h selected hselected)

/-! ## Closed p03 computations -/

def p03CollisionScore (form : P03NormalForm) (p : WeightThreeParameter) : ℕ :=
  collisionDegree p.word (p03NormalFormGenerators form)

def rankThreeCollisionCertificate : CollisionCertificate where
  degree0 := 9288
  degree1 := 540
  degree2 := 0
  degree3 := 0
  baseDegree := 1
  maximumDegree := 1
  exceptionalCap := 0
  selectedCap := 24
  degreeSumBound := 24
  edgeUpperBound := 12

def rankTwo0CollisionCertificate : CollisionCertificate where
  degree0 := 9288
  degree1 := 540
  degree2 := 0
  degree3 := 0
  baseDegree := 1
  maximumDegree := 1
  exceptionalCap := 0
  selectedCap := 24
  degreeSumBound := 24
  edgeUpperBound := 12

def rankTwo1CollisionCertificate : CollisionCertificate where
  degree0 := 9290
  degree1 := 537
  degree2 := 0
  degree3 := 1
  baseDegree := 1
  maximumDegree := 3
  exceptionalCap := 1
  selectedCap := 24
  degreeSumBound := 26
  edgeUpperBound := 13

def rankTwo2CollisionCertificate : CollisionCertificate where
  degree0 := 9376
  degree1 := 372
  degree2 := 72
  degree3 := 8
  baseDegree := 2
  maximumDegree := 3
  exceptionalCap := 8
  selectedCap := 24
  degreeSumBound := 56
  edgeUpperBound := 28

def p03CollisionCertificate : P03NormalForm → CollisionCertificate
  | .rankTwo0 => rankTwo0CollisionCertificate
  | .rankTwo1 => rankTwo1CollisionCertificate
  | .rankTwo2 => rankTwo2CollisionCertificate
  | .rankThree => rankThreeCollisionCertificate

/-- A six-loop word constructor keeps kernel reduction depth bounded: each
loop ranges over only fourteen or three elements. -/
def canonicalWeightThreeWord (i j k : Fin 14) (a b c : Fin 3) :
    CollisionWord :=
  fun q =>
    if q = i then nonzeroLabel a
    else if q = j then nonzeroLabel b
    else if q = k then nonzeroLabel c
    else .I

/-- Finite pointwise checker over all sorted supports and nonzero labels. -/
def checkPointwiseMaximum (translations : List CollisionWord) (maximum : ℕ) : Bool :=
  decide (∀ i j k : Fin 14, ∀ a b c : Fin 3,
    i < j ∧ j < k →
      collisionDegree (canonicalWeightThreeWord i j k a b c) translations ≤ maximum)

/-- Soundness of the bounded-depth pointwise checker. -/
theorem checkPointwiseMaximum_sound (translations : List CollisionWord) (maximum : ℕ)
    (h : checkPointwiseMaximum translations maximum = true) :
    ∀ i j k : Fin 14, ∀ a b c : Fin 3,
      i < j ∧ j < k →
        collisionDegree (canonicalWeightThreeWord i j k a b c) translations ≤ maximum := by
  exact of_decide_eq_true (by simpa [checkPointwiseMaximum] using h)

/- The concrete propositions `checkPointwiseMaximum generators maximum = true`
are not asserted here. They provide optional exact-table cross-checks and are
not load-bearing dependencies of the final theorem. -/

/-- The proposed certificate field definitionally matches the arithmetic
layer's recorded number.  This does not prove that the certificate is valid. -/
theorem p03CollisionCertificate_edgeUpperBound (form : P03NormalForm) :
    (p03CollisionCertificate form).edgeUpperBound = p03CollisionUpperBound form := by
  cases form <;> rfl



end Quantum1435
