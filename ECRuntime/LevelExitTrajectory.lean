import ECRuntime.LevelExitTail
import ECRuntime.FiniteMarginalIdentification
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-!
# Stage 26 fix 16: from one-level recursion to the actual trajectory tail

`LevelExitTail.lean` proves a geometric upper bound for the finite-state recursion
`finiteLevelSurvival`.  This file identifies that recursion with an event under the
actual Ionescu--Tulcea trajectory law and then with the strict natural-threshold tail
of the conventional first hitting time of the complement of the level.

The proof is deliberately split into three reusable bridges.

1. A finite trajectory stays in the level exactly when the initial state and every
   post-initial coordinate in the finite path lie in the level.  Summing the explicit
   Stage-15 path weights over this event gives exactly `finiteLevelSurvival`.
2. Stage 22's finite-marginal theorem transports that event mass to
   `transitionTrajectoryMeasure`.
3. The event is pointwise equivalent to the strict tail
   `k < transitionTrajectoryFirstHittingTime levelᶜ x path`.

Consequently the local exit-mass hypothesis from `LevelExitTail.lean` yields a genuine
`HasGeometricTailBound` certificate for the actual level-exit hitting time.
-/

/-- Finite post-initial paths which, together with the supplied initial state, remain
inside `level` through horizon `t`. -/
def finiteLevelSurvivalEvent {α : Type*}
    (level : Set α) (x : α) (t : ℕ) : Set (FiniteTrajectory α t) :=
  {path | x ∈ level ∧ ∀ i, path i ∈ level}

/-- Real `0/1` indicator of `finiteLevelSurvivalEvent`. -/
noncomputable def finiteLevelSurvivalIndicator {α : Type*}
    (level : Set α) (x : α) (t : ℕ) (path : FiniteTrajectory α t) : ℝ := by
  classical
  exact if path ∈ finiteLevelSurvivalEvent level x t then 1 else 0

/-- Explicit real path mass of surviving in `level` through horizon `t`. -/
noncomputable def finiteLevelSurvivalPathMass {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α) (t : ℕ) (x : α) : ℝ :=
  ∑ path : FiniteTrajectory α t,
    finiteTrajectoryWeight P t x path *
      finiteLevelSurvivalIndicator level x t path

/-- Membership in the survival event for a cons path separates into the current-state
condition and survival of the tail started from the first next state. -/
@[simp] theorem finiteLevelSurvivalEvent_cons_iff
    {α : Type*} (level : Set α) (x y : α) (t : ℕ)
    (tail : FiniteTrajectory α t) :
    Fin.cons y tail ∈ finiteLevelSurvivalEvent level x (t + 1) ↔
      x ∈ level ∧ tail ∈ finiteLevelSurvivalEvent level y t := by
  constructor
  · rintro ⟨hx, hall⟩
    have hy : y ∈ level := by
      simpa using hall (0 : Fin (t + 1))
    have htail : ∀ j : Fin t, tail j ∈ level := by
      intro j
      simpa using hall j.succ
    exact ⟨hx, hy, htail⟩
  · rintro ⟨hx, hy, htail⟩
    refine ⟨hx, ?_⟩
    intro i
    exact Fin.cases (by simpa using hy) (fun j => by simpa using htail j) i

/-- The real survival indicator inherits the same one-step decomposition. -/
@[simp] theorem finiteLevelSurvivalIndicator_cons
    {α : Type*} (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (x y : α) (t : ℕ)
    (tail : FiniteTrajectory α t) :
    finiteLevelSurvivalIndicator level x (t + 1) (Fin.cons y tail) =
      if x ∈ level then finiteLevelSurvivalIndicator level y t tail else 0 := by
  classical
  unfold finiteLevelSurvivalIndicator
  rw [finiteLevelSurvivalEvent_cons_iff]
  by_cases hx : x ∈ level <;> simp [hx]

/-- The finite survival indicator is nonnegative. -/
theorem finiteLevelSurvivalIndicator_nonneg
    {α : Type*} (level : Set α) (x : α) (t : ℕ)
    (path : FiniteTrajectory α t) :
    0 ≤ finiteLevelSurvivalIndicator level x t path := by
  classical
  unfold finiteLevelSurvivalIndicator
  split_ifs <;> norm_num

/-- Horizon-zero explicit survival mass. -/
@[simp] theorem finiteLevelSurvivalPathMass_zero
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (x : α) :
    finiteLevelSurvivalPathMass P level 0 x =
      if x ∈ level then 1 else 0 := by
  classical
  unfold finiteLevelSurvivalPathMass finiteLevelSurvivalIndicator
  by_cases hx : x ∈ level <;>
    simp [finiteLevelSurvivalEvent, finiteTrajectoryWeight, hx]

/-- The explicit path mass satisfies the same one-step recursion as
`finiteLevelSurvival`. -/
theorem finiteLevelSurvivalPathMass_succ
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (t : ℕ) (x : α) :
    finiteLevelSurvivalPathMass P level (t + 1) x =
      if x ∈ level then
        ∑ y, P x y * finiteLevelSurvivalPathMass P level t y
      else
        0 := by
  classical
  unfold finiteLevelSurvivalPathMass
  rw [sum_finiteTrajectory_succ]
  by_cases hx : x ∈ level
  · rw [if_pos hx]
    apply Finset.sum_congr rfl
    intro y _hy
    calc
      (∑ tail : FiniteTrajectory α t,
          finiteTrajectoryWeight P (t + 1) x (Fin.cons y tail) *
            finiteLevelSurvivalIndicator level x (t + 1) (Fin.cons y tail)) =
          ∑ tail : FiniteTrajectory α t,
            (P x y * finiteTrajectoryWeight P t y tail) *
              finiteLevelSurvivalIndicator level y t tail := by
        apply Finset.sum_congr rfl
        intro tail _htail
        rw [finiteTrajectoryWeight_cons]
        rw [finiteLevelSurvivalIndicator_cons]
        rw [if_pos hx]
      _ = P x y *
          (∑ tail : FiniteTrajectory α t,
            finiteTrajectoryWeight P t y tail *
              finiteLevelSurvivalIndicator level y t tail) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tail _htail
        ring
      _ = P x y * finiteLevelSurvivalPathMass P level t y := by
        rfl
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _hy
    apply Finset.sum_eq_zero
    intro tail _htail
    rw [finiteLevelSurvivalIndicator_cons]
    simp [hx]

/-- The explicit Stage-15 path sum for the finite survival event is exactly the recursive
quantity introduced in `LevelExitTail.lean`. -/
theorem finiteLevelSurvivalPathMass_eq_finiteLevelSurvival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)] :
    ∀ t x,
      finiteLevelSurvivalPathMass P level t x =
        finiteLevelSurvival P level t x := by
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvivalPathMass_zero, if_pos hx,
            finiteLevelSurvival_zero_of_mem P level x hx]
      · rw [finiteLevelSurvivalPathMass_zero, if_neg hx,
            finiteLevelSurvival_zero_of_not_mem P level x hx]
  | succ t ih =>
      intro x
      rw [finiteLevelSurvivalPathMass_succ]
      by_cases hx : x ∈ level
      · rw [if_pos hx, finiteLevelSurvival_succ_of_mem P level t x hx]
        apply Finset.sum_congr rfl
        intro y _hy
        rw [ih y]
      · rw [if_neg hx, finiteLevelSurvival_succ_of_not_mem P level t x hx]

/-- Every finite-level survival event is measurable on the finite path space. -/
theorem measurableSet_finiteLevelSurvivalEvent
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (level : Set α) (x : α) (t : ℕ) :
    MeasurableSet (finiteLevelSurvivalEvent level x t) := by
  exact (finiteLevelSurvivalEvent level x t).to_countable.measurableSet

/-- The explicit finite trajectory measure assigns the recursive survival quantity to
`finiteLevelSurvivalEvent`. -/
theorem finiteTrajectoryMeasure_finiteLevelSurvivalEvent
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (hP : IsStochastic P) (t : ℕ) (x : α) :
    finiteTrajectoryMeasure P hP t x
        (finiteLevelSurvivalEvent level x t) =
      ENNReal.ofReal (finiteLevelSurvival P level t x) := by
  classical
  have hEvent : MeasurableSet (finiteLevelSurvivalEvent level x t) :=
    measurableSet_finiteLevelSurvivalEvent level x t
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP t x]
  have hterm :
      ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory α t)),
        0 ≤ finiteTrajectoryWeight P t x path *
          finiteLevelSurvivalIndicator level x t path := by
    intro path _hpath
    exact mul_nonneg
      (finiteTrajectoryWeight_nonneg P hP t x path)
      (finiteLevelSurvivalIndicator_nonneg level x t path)
  calc
    (∑ path : FiniteTrajectory α t,
        (finiteLevelSurvivalEvent level x t).indicator
            (fun _ => (1 : ENNReal)) path *
          ENNReal.ofReal (finiteTrajectoryWeight P t x path)) =
        ∑ path : FiniteTrajectory α t,
          ENNReal.ofReal
            (finiteTrajectoryWeight P t x path *
              finiteLevelSurvivalIndicator level x t path) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hmem : path ∈ finiteLevelSurvivalEvent level x t
      · simp [finiteLevelSurvivalIndicator, hmem]
      · simp [finiteLevelSurvivalIndicator, hmem]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory α t,
          finiteTrajectoryWeight P t x path *
            finiteLevelSurvivalIndicator level x t path) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hterm
    _ = ENNReal.ofReal (finiteLevelSurvivalPathMass P level t x) := by
      rfl
    _ = ENNReal.ofReal (finiteLevelSurvival P level t x) := by
      rw [finiteLevelSurvivalPathMass_eq_finiteLevelSurvival P level t x]

/-- Infinite trajectories whose supplied initial state and first `t` post-initial states
all remain in `level`.  The definition is intentionally a preimage under the verified
finite-tail projection. -/
def transitionLevelSurvivalEvent {α : Type*}
    (level : Set α) (x : α) (t : ℕ) : Set (ℕ → α) :=
  transitionTrajectoryTail t ⁻¹' finiteLevelSurvivalEvent level x t

/-- The infinite-trajectory survival event is measurable. -/
theorem measurableSet_transitionLevelSurvivalEvent
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (level : Set α) (x : α) (t : ℕ) :
    MeasurableSet (transitionLevelSurvivalEvent level x t) := by
  unfold transitionLevelSurvivalEvent
  exact (measurableSet_finiteLevelSurvivalEvent level x t).preimage
    (measurable_transitionTrajectoryTail (α := α) t)

/-- Event semantics in conventional absolute time: surviving through horizon `t` means
that every state at times `0,...,t` lies in `level`. -/
theorem mem_transitionLevelSurvivalEvent_iff
    {α : Type*} (level : Set α) (x : α) (t : ℕ) (path : ℕ → α) :
    path ∈ transitionLevelSurvivalEvent level x t ↔
      ∀ j, j ≤ t → transitionTrajectoryState x path j ∈ level := by
  change
    (x ∈ level ∧ ∀ i : Fin t, path (i.val + 1) ∈ level) ↔
      ∀ j, j ≤ t → transitionTrajectoryState x path j ∈ level
  constructor
  · rintro ⟨hx, htail⟩ j hj
    cases j with
    | zero =>
        simpa using hx
    | succ j =>
        have hjlt : j < t := by omega
        have h := htail ⟨j, hjlt⟩
        simpa using h
  · intro h
    constructor
    · simpa using h 0 (Nat.zero_le t)
    · intro i
      have hi := h (i.val + 1) (by omega)
      simpa using hi

/-- Under the actual Ionescu--Tulcea trajectory law, finite survival has exactly the
recursive mass from `LevelExitTail.lean`. -/
theorem transitionTrajectoryMeasure_transitionLevelSurvivalEvent
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (hP : IsStochastic P) (t : ℕ) (x : α) :
    transitionTrajectoryMeasure P hP x
        (transitionLevelSurvivalEvent level x t) =
      ENNReal.ofReal (finiteLevelSurvival P level t x) := by
  have htail : Measurable (transitionTrajectoryTail (α := α) t) :=
    measurable_transitionTrajectoryTail (α := α) t
  have hEvent : MeasurableSet (finiteLevelSurvivalEvent level x t) :=
    measurableSet_finiteLevelSurvivalEvent level x t
  unfold transitionLevelSurvivalEvent
  rw [← Measure.map_apply htail hEvent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]
  exact finiteTrajectoryMeasure_finiteLevelSurvivalEvent P level hP t x

/-- Natural thresholds of the conventional first hitting time of `levelᶜ` are exactly
finite survival in `level`. -/
theorem natCast_lt_transitionTrajectoryFirstHittingTime_compl_iff
    {α : Type*} (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (x : α) (path : ℕ → α) (k : ℕ) :
    (k : ENNReal) <
        transitionTrajectoryFirstHittingTime (levelᶜ) x path ↔
      ∀ j, j ≤ k → transitionTrajectoryState x path j ∈ level := by
  classical
  unfold transitionTrajectoryFirstHittingTime
  by_cases h : ∃ n, transitionTrajectoryState x path n ∈ levelᶜ
  · rw [dif_pos h]
    have hcast :
        ENNReal.ofReal (Nat.find h : ℝ) = (Nat.find h : ENNReal) := by
      simp
    rw [hcast]
    constructor
    · intro hk j hj
      have hkNat : k < Nat.find h := by
        exact_mod_cast hk
      have hjFind : j < Nat.find h := lt_of_le_of_lt hj hkNat
      have hnotTarget := Nat.find_min h hjFind
      simpa using hnotTarget
    · intro hall
      have hkFind : k < Nat.find h := by
        by_contra hnot
        have hFindLe : Nat.find h ≤ k := Nat.le_of_not_gt hnot
        have hlevel := hall (Nat.find h) hFindLe
        have htarget := Nat.find_spec h
        exact htarget hlevel
      exact_mod_cast hkFind
  · rw [dif_neg h]
    constructor
    · intro _hk j _hj
      by_contra hnotLevel
      apply h
      refine ⟨j, ?_⟩
      simpa using hnotLevel
    · intro _hall
      simp

/-- The strict natural-threshold tail event of level exit is exactly the finite survival
event already identified with `finiteLevelSurvival`. -/
theorem runtimeTailEvent_transitionTrajectoryLevelExit_nat
    {α : Type*} (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (x : α) (k : ℕ) :
    runtimeTailEvent
        (transitionTrajectoryFirstHittingTime (levelᶜ) x)
        (k : ENNReal) =
      transitionLevelSurvivalEvent level x k := by
  ext path
  change
    ((k : ENNReal) < transitionTrajectoryFirstHittingTime (levelᶜ) x path) ↔
      path ∈ transitionLevelSurvivalEvent level x k
  rw [natCast_lt_transitionTrajectoryFirstHittingTime_compl_iff level x path k]
  exact (mem_transitionLevelSurvivalEvent_iff level x k path).symm

/-- Exact natural-threshold tail mass of the actual level-exit hitting time. -/
theorem transitionTrajectoryLevelExit_tailMass_eq_finiteLevelSurvival
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (hP : IsStochastic P) (x : α) (k : ℕ) :
    runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (levelᶜ) x)
        (k : ENNReal) =
      ENNReal.ofReal (finiteLevelSurvival P level k x) := by
  unfold runtimeTailMass
  rw [runtimeTailEvent_transitionTrajectoryLevelExit_nat level x k]
  exact transitionTrajectoryMeasure_transitionLevelSurvivalEvent
    P level hP k x

/-- A uniform one-step exit-mass lower bound yields a genuine geometric tail certificate
for the conventional level-exit hitting time under the Ionescu--Tulcea trajectory law. -/
theorem hasGeometricTailBound_transitionTrajectoryLevelExit
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (hP : IsStochastic P) (p : unitInterval)
    (hexit : ∀ z, z ∈ level →
      (p : ℝ) ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) :
    HasGeometricTailBound
      (transitionTrajectoryMeasure P hP x)
      (transitionTrajectoryFirstHittingTime (levelᶜ) x)
      p := by
  intro k
  rw [transitionTrajectoryLevelExit_tailMass_eq_finiteLevelSurvival
    P level hP x k]
  exact finiteLevelSurvival_ofReal_le_geometricSurvival_of_exit_mass
    P level hP p hexit k x hx

end ECRuntime
