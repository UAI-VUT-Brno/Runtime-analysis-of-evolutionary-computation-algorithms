import ECRuntime.MultiLevelCoupledTrajectory
import ECRuntime.GeometricRuntime
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 26 fix 28: geometric waiting extraction from Bernoulli-vector prefixes

`MultiLevelCoupledTrajectory.lean` establishes the finite-dimensional comparison law
needed by the stochastic fitness-level coupling: from every current state, the emitted
`Fin m -> Bool` label vector has the same product-Bernoulli marginal, and finite label
prefixes are therefore i.i.d. even though the real state trajectory remains adaptive.

This file identifies the first-success waiting law of an arbitrary coordinate of that
comparison vector.  The proof is deliberately finite-dimensional.  First, a generic
coordinate-pattern indicator is introduced and its mass under the i.i.d. vector-label
weight is shown to be exactly the corresponding one-dimensional Bernoulli path weight.
Specializing the pattern to `n` failures followed by one success gives the exact mass
`(1-p)^n p`.  The same identity is then transferred to the finite multi-level coupled
state/label law from every supplied restart state.

The final theorem compares this real-valued coupled-prefix mass with the singleton mass
of Mathlib's canonical geometric failure-count measure.  Thus a residence interval
started at any fixed entry state already has the exact comparison waiting law required
by the geometric product construction.  The remaining Stage-26 step is to make the
restart time history-dependent, prove the coordinatewise residence inequalities on the
joint support, and assemble the product coupling consumed by `CouplingDomination.lean`.
-/

/-- A zero-one weight saying that coordinate `i` of `bits` equals the requested bit. -/
def bernoulliCoordinateMatch {m : ℕ}
    (i : Fin m) (b : Bool) (bits : Fin m → Bool) : ℝ :=
  if bits i = b then 1 else 0

/-- One coordinate of the product-Bernoulli vector has exactly its Bernoulli marginal.
The indicator form is convenient for later finite-path event sums. -/
theorem sum_bernoulliLevelVectorWeight_mul_coordinateMatch
    {m : ℕ} (p : Fin m → ℝ) (i : Fin m) (b : Bool) :
    (∑ bits : Fin m → Bool,
      bernoulliLevelVectorWeight p bits * bernoulliCoordinateMatch i b bits) =
      bernoulliBoolWeight (p i) b := by
  classical
  let f : (j : Fin m) → Bool → ℝ := fun j c =>
    if j = i then
      bernoulliBoolWeight (p j) c * (if c = b then 1 else 0)
    else
      bernoulliBoolWeight (p j) c
  have hpoint : ∀ bits : Fin m → Bool,
      (∏ j : Fin m, f j (bits j)) =
        bernoulliLevelVectorWeight p bits * bernoulliCoordinateMatch i b bits := by
    intro bits
    rw [Fintype.prod_eq_mul_prod_compl i (fun j : Fin m => f j (bits j))]
    rw [bernoulliLevelVectorWeight_eq_active_mul_complement p i bits]
    have hcomp :
        (∏ j ∈ ({i}ᶜ : Finset (Fin m)), f j (bits j)) =
          bernoulliLevelVectorComplementWeight p i bits := by
      unfold bernoulliLevelVectorComplementWeight
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [f, hji]
    rw [hcomp]
    simp [f, bernoulliCoordinateMatch]
  have hprodSum :
      (∑ bits : Fin m → Bool, ∏ j : Fin m, f j (bits j)) =
        ∏ j : Fin m, ∑ c : Bool, f j c := by
    symm
    exact Fintype.prod_sum f
  calc
    (∑ bits : Fin m → Bool,
        bernoulliLevelVectorWeight p bits * bernoulliCoordinateMatch i b bits) =
        ∑ bits : Fin m → Bool, ∏ j : Fin m, f j (bits j) := by
      apply Finset.sum_congr rfl
      intro bits _hbits
      exact (hpoint bits).symm
    _ = ∏ j : Fin m, ∑ c : Bool, f j c := hprodSum
    _ = ∑ c : Bool, f i c := by
      apply Finset.prod_eq_single i
      · intro j _hj hji
        simp [f, hji]
      · intro hi
        simp at hi
    _ = bernoulliBoolWeight (p i) b := by
      cases b <;> simp [f, bernoulliBoolWeight]

/-- Coordinatewise path indicator: every emitted vector coordinate `i` must agree with
`pattern` throughout the supplied finite prefix. -/
def finiteCoordinatePatternIndicator {m : ℕ} (i : Fin m) :
    (t : ℕ) → FiniteTrajectory (Fin m → Bool) t → FiniteTrajectory Bool t → ℝ
  | 0, _labels, _pattern => 1
  | t + 1, labels, pattern =>
      bernoulliCoordinateMatch i (pattern 0) (labels 0) *
        finiteCoordinatePatternIndicator i t (Fin.tail labels) (Fin.tail pattern)

@[simp] theorem finiteCoordinatePatternIndicator_cons
    {m t : ℕ} (i : Fin m)
    (bits : Fin m → Bool) (labels : FiniteTrajectory (Fin m → Bool) t)
    (b : Bool) (pattern : FiniteTrajectory Bool t) :
    finiteCoordinatePatternIndicator i (t + 1)
        (Fin.cons bits labels) (Fin.cons b pattern) =
      bernoulliCoordinateMatch i b bits *
        finiteCoordinatePatternIndicator i t labels pattern := by
  rfl

/-- Under the i.i.d. product-Bernoulli vector law, prescribing one coordinate through
an arbitrary finite Boolean pattern has exactly the corresponding one-dimensional
i.i.d. Bernoulli path weight. -/
theorem finiteIIDLabelWeight_coordinatePattern_mass
    {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    ∀ t (pattern : FiniteTrajectory Bool t),
      (∑ labels : FiniteTrajectory (Fin m → Bool) t,
        finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t labels *
          finiteCoordinatePatternIndicator i t labels pattern) =
        finiteIIDLabelWeight (bernoulliBoolWeight (p i)) t pattern := by
  intro t
  induction t with
  | zero =>
      intro pattern
      simp [finiteIIDLabelWeight, finiteCoordinatePatternIndicator]
  | succ t ih =>
      intro pattern
      rw [← Fin.cons_self_tail pattern]
      rw [sum_finiteTrajectory_succ]
      simp_rw [finiteIIDLabelWeight_cons, finiteCoordinatePatternIndicator_cons]
      calc
        (∑ bits : Fin m → Bool,
            ∑ tail : FiniteTrajectory (Fin m → Bool) t,
              (bernoulliLevelVectorWeight p bits *
                  finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t tail) *
                (bernoulliCoordinateMatch i (pattern 0) bits *
                  finiteCoordinatePatternIndicator i t tail (Fin.tail pattern))) =
            ∑ bits : Fin m → Bool,
              (bernoulliLevelVectorWeight p bits *
                bernoulliCoordinateMatch i (pattern 0) bits) *
                (∑ tail : FiniteTrajectory (Fin m → Bool) t,
                  finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t tail *
                    finiteCoordinatePatternIndicator i t tail (Fin.tail pattern)) := by
          apply Finset.sum_congr rfl
          intro bits _hbits
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tail _htail
          ring
        _ = ∑ bits : Fin m → Bool,
              (bernoulliLevelVectorWeight p bits *
                bernoulliCoordinateMatch i (pattern 0) bits) *
                finiteIIDLabelWeight (bernoulliBoolWeight (p i)) t
                  (Fin.tail pattern) := by
          rw [ih (Fin.tail pattern)]
        _ = (∑ bits : Fin m → Bool,
              bernoulliLevelVectorWeight p bits *
                bernoulliCoordinateMatch i (pattern 0) bits) *
              finiteIIDLabelWeight (bernoulliBoolWeight (p i)) t
                (Fin.tail pattern) := by
          rw [Finset.sum_mul]
        _ = bernoulliBoolWeight (p i) (pattern 0) *
              finiteIIDLabelWeight (bernoulliBoolWeight (p i)) t
                (Fin.tail pattern) := by
          rw [sum_bernoulliLevelVectorWeight_mul_coordinateMatch]
        _ = finiteIIDLabelWeight (bernoulliBoolWeight (p i)) (t + 1)
              (Fin.cons (pattern 0) (Fin.tail pattern)) := by
          rfl

/-- The finite Boolean pattern consisting of `n` failures followed by one success. -/
def firstSuccessBoolPattern :
    (n : ℕ) → FiniteTrajectory Bool (n + 1)
  | 0 => fun _ => true
  | n + 1 => Fin.cons false (firstSuccessBoolPattern n)

@[simp] theorem firstSuccessBoolPattern_zero :
    firstSuccessBoolPattern 0 = (fun _ : Fin 1 => true) := by
  rfl

@[simp] theorem firstSuccessBoolPattern_succ (n : ℕ) :
    firstSuccessBoolPattern (n + 1) =
      Fin.cons false (firstSuccessBoolPattern n) := by
  rfl

/-- Exact one-dimensional weight of `n` failures followed by one success. -/
theorem finiteIIDLabelWeight_firstSuccessBoolPattern
    (p : ℝ) (n : ℕ) :
    finiteIIDLabelWeight (bernoulliBoolWeight p) (n + 1)
        (firstSuccessBoolPattern n) =
      (1 - p) ^ n * p := by
  induction n with
  | zero =>
      simp [firstSuccessBoolPattern, finiteIIDLabelWeight, bernoulliBoolWeight]
  | succ n ih =>
      rw [firstSuccessBoolPattern_succ]
      rw [finiteIIDLabelWeight_cons]
      simp [bernoulliBoolWeight, ih, pow_succ]
      ring

/-- Exact first-success mass of coordinate `i` under a finite i.i.d. vector-label prefix. -/
theorem finiteIIDLabelWeight_coordinateFirstSuccess_mass
    {m : ℕ} (p : Fin m → ℝ) (i : Fin m) (n : ℕ) :
    (∑ labels : FiniteTrajectory (Fin m → Bool) (n + 1),
      finiteIIDLabelWeight (bernoulliLevelVectorWeight p) (n + 1) labels *
        finiteCoordinatePatternIndicator i (n + 1) labels
          (firstSuccessBoolPattern n)) =
      (1 - p i) ^ n * p i := by
  rw [finiteIIDLabelWeight_coordinatePattern_mass p i]
  exact finiteIIDLabelWeight_firstSuccessBoolPattern (p i) n

/-- Real-valued mass of a prescribed coordinate pattern under the finite adaptive
multi-level coupled state/label law.  State paths have already been summed out. -/
noncomputable def finiteMultiLevelCoordinatePatternMass
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ)
    (x : α) (i : Fin m)
    (t : ℕ) (pattern : FiniteTrajectory Bool t) : ℝ :=
  ∑ labels : FiniteTrajectory (Fin m → Bool) t,
    (∑ states : FiniteTrajectory α t,
      finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
        (zipFiniteTrajectories states labels)) *
      finiteCoordinatePatternIndicator i t labels pattern

/-- The coordinate-pattern law remains exactly Bernoulli after the real adaptive state
path has been summed out.  Importantly, the formula holds from every supplied restart
state `x`. -/
theorem finiteMultiLevelCoordinatePatternMass_eq
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : α) (i : Fin m)
    (t : ℕ) (pattern : FiniteTrajectory Bool t) :
    finiteMultiLevelCoordinatePatternMass P V hbound p x i t pattern =
      finiteIIDLabelWeight (bernoulliBoolWeight (p i)) t pattern := by
  unfold finiteMultiLevelCoordinatePatternMass
  simp_rw [finiteMultiLevelBernoulliCoupledWeight_label_marginal
    P hP V hbound p hp hexit t x]
  exact finiteIIDLabelWeight_coordinatePattern_mass p i t pattern

/-- From every supplied restart state, coordinate `i` has exact mass `(1-p_i)^n p_i`
for `n` failures followed by one success.  This is the finite restart form of the
geometric comparison law. -/
theorem finiteMultiLevelCoordinateFirstSuccess_mass
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : α) (i : Fin m) (n : ℕ) :
    finiteMultiLevelCoordinatePatternMass P V hbound p x i (n + 1)
        (firstSuccessBoolPattern n) =
      (1 - p i) ^ n * p i := by
  rw [finiteMultiLevelCoordinatePatternMass_eq
    P hP V hbound p hp hexit x i (n + 1) (firstSuccessBoolPattern n)]
  exact finiteIIDLabelWeight_firstSuccessBoolPattern (p i) n

/-- Package a real probability parameter and its bounds as Mathlib's `unitInterval`. -/
def probabilityUnitInterval (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : unitInterval :=
  ⟨p, hp0, hp1⟩

@[simp] theorem coe_probabilityUnitInterval
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((probabilityUnitInterval p hp0 hp1 : unitInterval) : ℝ) = p := by
  rfl

/-- The finite coupled-prefix first-success mass is exactly the singleton mass of
Mathlib's canonical geometric failure-count law after embedding into `ENNReal`. -/
theorem finiteMultiLevelCoordinateFirstSuccess_mass_eq_geometricFailure_singleton
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : α) (i : Fin m) (n : ℕ) :
    ENNReal.ofReal
        (finiteMultiLevelCoordinatePatternMass P V hbound p x i (n + 1)
          (firstSuccessBoolPattern n)) =
      geometricFailureMeasure
        (probabilityUnitInterval (p i) (le_of_lt (hp i)) (hp1 i)) {n} := by
  rw [finiteMultiLevelCoordinateFirstSuccess_mass
    P hP V hbound p hp hexit x i n]
  let q : unitInterval :=
    probabilityUnitInterval (p i) (le_of_lt (hp i)) (hp1 i)
  have hq : q ≠ 0 := by
    intro hzero
    have hcoe := congrArg (fun r : unitInterval => (r : ℝ)) hzero
    have hpne : p i ≠ 0 := ne_of_gt (hp i)
    apply hpne
    simpa [q, probabilityUnitInterval] using hcoe
  symm
  simpa [q, probabilityUnitInterval] using
    (geometricFailureMeasure_singleton (p := q) hq n)

end ECRuntime
