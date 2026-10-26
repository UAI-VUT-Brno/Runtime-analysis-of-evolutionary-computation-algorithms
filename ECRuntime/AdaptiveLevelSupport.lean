import ECRuntime.BernoulliWaitingExtraction
import ECRuntime.LevelResidence
import Mathlib

namespace ECRuntime

/-!
# Adaptive exact-level support for the multi-level Bernoulli coupling

Stage 26 fix 30 isolates the support fact needed after the fixed-restart
geometric extraction verified in fix 29.

If the current potential is exactly `i+1`, then the adaptive multi-level
coupling really uses coordinate `i`.  A success on that active coordinate has
zero coupled weight on any transition that remains in the same exact level.
Consequently positive coupled weight with an active success forces a genuine
level exit.

This file deliberately stops at the one-step support interface.  The next
layer can combine it with the contiguous residence interval from
`LevelResidence.lean` and lift the statement through finite coupled path
products before handling the history-dependent first entry time.
-/

/-- If a bounded positive potential has value `i+1`, its adaptive coordinate
is exactly `i`. -/
theorem activePositivePotentialLevelIndex_eq_of_value
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (x : α) (hx0 : V x ≠ 0) (i : Fin m)
    (hx : V x = i.1 + 1) :
    activePositivePotentialLevelIndex V hbound x hx0 = i := by
  apply Fin.ext
  have hactive := activePositivePotentialLevelIndex_value V hbound x hx0
  omega

/-- Membership in the exact positive level identifies the adaptive coordinate. -/
theorem activePositivePotentialLevelIndex_eq_of_mem_exactPositivePotentialLevel
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (x : α) (hx0 : V x ≠ 0) (i : Fin m)
    (hx : x ∈ exactPositivePotentialLevel V i) :
    activePositivePotentialLevelIndex V hbound x hx0 = i := by
  exact activePositivePotentialLevelIndex_eq_of_value
    V hbound x hx0 i ((mem_exactPositivePotentialLevel V i x).1 hx)

/-- At a state in exact positive level `i+1`, the global adaptive step is the
fixed active-coordinate vector step for coordinate `i`. -/
theorem multiLevelBernoulliCoupledStepWeight_eq_level_of_mem_exactPositivePotentialLevel
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hx : x ∈ exactPositivePotentialLevel V i) :
    multiLevelBernoulliCoupledStepWeight P V hbound p x y bits =
      levelBernoulliVectorCoupledStepWeight
        P (exactPositivePotentialLevel V i) p i x y bits := by
  classical
  have hxval : V x = i.1 + 1 :=
    (mem_exactPositivePotentialLevel V i x).1 hx
  have hx0 : V x ≠ 0 := by omega
  have hactive :
      activePositivePotentialLevelIndex V hbound x hx0 = i :=
    activePositivePotentialLevelIndex_eq_of_value
      V hbound x hx0 i hxval
  simp [multiLevelBernoulliCoupledStepWeight, hx0, hactive]

/-- The fixed-level scalar coupling assigns zero success weight to a transition
that starts and ends inside the level.  The current-state hypothesis selects
the substantive exit split rather than the independent outside-level branch. -/
theorem levelBernoulliCoupledStepWeight_success_eq_zero_of_stay
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α) (p : ℝ)
    (x y : α) (hx : x ∈ level) (hy : y ∈ level) :
    levelBernoulliCoupledStepWeight P level p x y true = 0 := by
  classical
  simp [levelBernoulliCoupledStepWeight, hx,
    transitionLevelExitBernoulliSplit_success_eq_zero_of_stay P level p x y hy]

/-- In the full Bernoulli vector step, success of the active coordinate has
zero weight whenever the real transition stays in the active level. -/
theorem levelBernoulliVectorCoupledStepWeight_eq_zero_of_stay_success
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hx : x ∈ level) (hy : y ∈ level)
    (hbit : bits i = true) :
    levelBernoulliVectorCoupledStepWeight P level p i x y bits = 0 := by
  rw [levelBernoulliVectorCoupledStepWeight_eq_active_mul_complement]
  rw [hbit]
  rw [levelBernoulliCoupledStepWeight_success_eq_zero_of_stay
    P level (p i) x y hx hy]
  simp

/-- The adaptive multi-level step has zero weight on a same-level transition
when the coordinate representing that level reports success. -/
theorem multiLevelBernoulliCoupledStepWeight_eq_zero_of_exactLevel_stay_success
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hx : x ∈ exactPositivePotentialLevel V i)
    (hy : y ∈ exactPositivePotentialLevel V i)
    (hbit : bits i = true) :
    multiLevelBernoulliCoupledStepWeight P V hbound p x y bits = 0 := by
  rw [multiLevelBernoulliCoupledStepWeight_eq_level_of_mem_exactPositivePotentialLevel
    P V hbound p i x y bits hx]
  exact levelBernoulliVectorCoupledStepWeight_eq_zero_of_stay_success
    P (exactPositivePotentialLevel V i) p i x y bits hx hy hbit

/-- Positive adaptive coupled weight together with active-coordinate success
forces the next state to leave the current exact positive level. -/
theorem multiLevelBernoulliCoupledStepWeight_active_success_forces_exactLevel_exit
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hx : x ∈ exactPositivePotentialLevel V i)
    (hbit : bits i = true)
    (hpositive : 0 < multiLevelBernoulliCoupledStepWeight
      P V hbound p x y bits) :
    y ∉ exactPositivePotentialLevel V i := by
  intro hy
  have hzero :=
    multiLevelBernoulliCoupledStepWeight_eq_zero_of_exactLevel_stay_success
      P V hbound p i x y bits hx hy hbit
  rw [hzero] at hpositive
  exact (lt_irrefl 0) hpositive

end ECRuntime
