import ECRuntime.PreEntryCoordinateFreshness
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 33: prefix factorization up to the random first entry

Stage 26 fix 32 fix 1 compiler-verifies the local structural fact needed for the
history-dependent freshness argument: strictly before the first visit of exact level
`i+1`, comparison coordinate `i` is inactive.  At every such transition the adaptive
coupled step factors into its ordinary Bernoulli weight at coordinate `i` times a
complement that is insensitive to the value of coordinate `i`.

This module iterates that one-step identity over an arbitrary finite prefix ending no
later than the actual first-entry time.  The resulting whole-prefix weight separates
exactly into

* the scalar Bernoulli path weight of coordinate `i`; and
* a complementary prefix factor that is unchanged if the entire pre-entry coordinate
  stream is replaced.

The endpoint is stated directly at `firstExactLevelEntryTime`.  It is the algebraic
finite-history interface needed for the next stage, where first-entry histories will be
summed and the already verified fixed-restart first-success/geometric law will be
restarted at the history-dependent entry state.
-/

/-- Product weight of a scalar Boolean Bernoulli stream over transition times
`0, ..., T-1`. -/
noncomputable def bernoulliBoolPrefixWeight
    (q : ℝ) (coord : ℕ → Bool) (T : ℕ) : ℝ :=
  ∏ t ∈ Finset.range T, bernoulliBoolWeight q (coord t)

@[simp] theorem bernoulliBoolPrefixWeight_zero
    (q : ℝ) (coord : ℕ → Bool) :
    bernoulliBoolPrefixWeight q coord 0 = 1 := by
  simp [bernoulliBoolPrefixWeight]

/-- Product of the adaptive state/vector-label coupled step weights over transition
indices `0, ..., T-1` along supplied complete state and label streams. -/
noncomputable def multiLevelBernoulliCoupledPrefixWeight
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (T : ℕ) : ℝ :=
  ∏ t ∈ Finset.range T,
    multiLevelBernoulliCoupledStepWeight
      P V hbound p
      (transitionTrajectoryState x path t)
      (transitionTrajectoryState x path (t + 1))
      (labels t)

@[simp] theorem multiLevelBernoulliCoupledPrefixWeight_zero
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) :
    multiLevelBernoulliCoupledPrefixWeight
      P V hbound p x path labels 0 = 1 := by
  simp [multiLevelBernoulliCoupledPrefixWeight]

/-- Product of the adaptive complements obtained after deleting coordinate `i` from
all transition factors in a finite prefix. -/
noncomputable def preEntryInactiveCoordinateComplementPrefixWeight
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (T : ℕ) : ℝ :=
  ∏ t ∈ Finset.range T,
    multiLevelBernoulliInactiveCoordinateComplementWeight
      P V hbound p i
      (transitionTrajectoryState x path t)
      (transitionTrajectoryState x path (t + 1))
      (labels t)

@[simp] theorem preEntryInactiveCoordinateComplementPrefixWeight_zero
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) :
    preEntryInactiveCoordinateComplementPrefixWeight
      P V hbound p i x path labels 0 = 1 := by
  simp [preEntryInactiveCoordinateComplementPrefixWeight]

/-- Replace one comparison coordinate at every transition time while leaving all other
coordinates unchanged. -/
def updateLabelCoordinateStream
    {m : ℕ}
    (labels : ℕ → (Fin m → Bool))
    (i : Fin m) (coord : ℕ → Bool) :
    ℕ → (Fin m → Bool) :=
  fun t => Function.update (labels t) i (coord t)

@[simp] theorem updateLabelCoordinateStream_apply_self
    {m : ℕ}
    (labels : ℕ → (Fin m → Bool))
    (i : Fin m) (coord : ℕ → Bool) (t : ℕ) :
    updateLabelCoordinateStream labels i coord t i = coord t := by
  simp [updateLabelCoordinateStream]

/-- Before first entry, the full coupled prefix weight factors into the scalar Bernoulli
prefix of coordinate `i` and the product of the omitted-coordinate complements.

The hypothesis `T ≤ firstExactLevelEntryTime ...` is exactly what is needed: every
transition index in `Finset.range T` is strictly before entry. -/
theorem multiLevelBernoulliCoupledPrefixWeight_eq_coordinate_mul_complement_before_firstEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (i : Fin m)
    (hvisit : ∃ s,
      V (transitionTrajectoryState x path s) = i.val + 1)
    (T : ℕ)
    (hT : T ≤ firstExactLevelEntryTime V x path i hvisit) :
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path labels T =
      bernoulliBoolPrefixWeight (p i) (fun t => labels t i) T *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T := by
  unfold multiLevelBernoulliCoupledPrefixWeight
    bernoulliBoolPrefixWeight
    preEntryInactiveCoordinateComplementPrefixWeight
  calc
    (∏ t ∈ Finset.range T,
      multiLevelBernoulliCoupledStepWeight
        P V hbound p
        (transitionTrajectoryState x path t)
        (transitionTrajectoryState x path (t + 1))
        (labels t)) =
      ∏ t ∈ Finset.range T,
        (bernoulliBoolWeight (p i) (labels t i) *
          multiLevelBernoulliInactiveCoordinateComplementWeight
            P V hbound p i
            (transitionTrajectoryState x path t)
            (transitionTrajectoryState x path (t + 1))
            (labels t)) := by
      apply Finset.prod_congr rfl
      intro t ht
      have htT : t < T := Finset.mem_range.mp ht
      have htEntry : t < firstExactLevelEntryTime V x path i hvisit :=
        lt_of_lt_of_le htT hT
      exact
        multiLevelBernoulliCoupledStepWeight_eq_inactiveCoordinate_mul_before_firstEntry
          P V hbound p x path i hvisit htEntry
          (transitionTrajectoryState x path (t + 1)) (labels t)
    _ =
      (∏ t ∈ Finset.range T, bernoulliBoolWeight (p i) (labels t i)) *
        (∏ t ∈ Finset.range T,
          multiLevelBernoulliInactiveCoordinateComplementWeight
            P V hbound p i
            (transitionTrajectoryState x path t)
            (transitionTrajectoryState x path (t + 1))
            (labels t)) := by
      rw [Finset.prod_mul_distrib]

/-- The whole complementary prefix is insensitive to replacing coordinate `i` at every
transition time.  This is the prefix-level form of the one-step complement invariance
from fix 32 fix 1. -/
theorem preEntryInactiveCoordinateComplementPrefixWeight_update_coordinate
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (coord : ℕ → Bool) (T : ℕ) :
    preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path
          (updateLabelCoordinateStream labels i coord) T =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels T := by
  unfold preEntryInactiveCoordinateComplementPrefixWeight
    updateLabelCoordinateStream
  apply Finset.prod_congr rfl
  intro t _ht
  exact
    multiLevelBernoulliInactiveCoordinateComplementWeight_update_self
      P V hbound p i
      (transitionTrajectoryState x path t)
      (transitionTrajectoryState x path (t + 1))
      (labels t) (coord t)

/-- Replacing the entire inactive coordinate stream in a prefix ending before first entry
changes the full coupled weight only through the scalar Bernoulli prefix weight of the
replacement stream. -/
theorem multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (i : Fin m)
    (hvisit : ∃ s,
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord : ℕ → Bool) (T : ℕ)
    (hT : T ≤ firstExactLevelEntryTime V x path i hvisit) :
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord) T =
      bernoulliBoolPrefixWeight (p i) coord T *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T := by
  calc
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord) T =
      bernoulliBoolPrefixWeight (p i)
          (fun t => updateLabelCoordinateStream labels i coord t i) T *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path
            (updateLabelCoordinateStream labels i coord) T :=
      multiLevelBernoulliCoupledPrefixWeight_eq_coordinate_mul_complement_before_firstEntry
        P V hbound p x path
        (updateLabelCoordinateStream labels i coord) i hvisit T hT
    _ = bernoulliBoolPrefixWeight (p i) coord T *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T := by
      have hcoord :
          bernoulliBoolPrefixWeight (p i)
              (fun t => updateLabelCoordinateStream labels i coord t i) T =
            bernoulliBoolPrefixWeight (p i) coord T := by
        unfold bernoulliBoolPrefixWeight
        apply Finset.prod_congr rfl
        intro t _ht
        simp
      rw [hcoord]
      rw [preEntryInactiveCoordinateComplementPrefixWeight_update_coordinate
        P V hbound p i x path labels coord T]

/-- Prefix factorization exactly at the actual history-dependent first-entry time. -/
theorem multiLevelBernoulliCoupledPrefixWeight_eq_coordinate_mul_complement_to_firstEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (i : Fin m)
    (hvisit : ∃ s,
      V (transitionTrajectoryState x path s) = i.val + 1) :
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path labels
          (firstExactLevelEntryTime V x path i hvisit) =
      bernoulliBoolPrefixWeight (p i) (fun t => labels t i)
          (firstExactLevelEntryTime V x path i hvisit) *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels
          (firstExactLevelEntryTime V x path i hvisit) := by
  exact
    multiLevelBernoulliCoupledPrefixWeight_eq_coordinate_mul_complement_before_firstEntry
      P V hbound p x path labels i hvisit
      (firstExactLevelEntryTime V x path i hvisit) le_rfl

/-- Replacement-stream form of the exact first-entry endpoint.  The complementary
first-entry history weight is shared by every possible pre-entry coordinate pattern. -/
theorem multiLevelBernoulliCoupledPrefixWeight_update_coordinate_to_firstEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (i : Fin m)
    (hvisit : ∃ s,
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord : ℕ → Bool) :
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord)
          (firstExactLevelEntryTime V x path i hvisit) =
      bernoulliBoolPrefixWeight (p i) coord
          (firstExactLevelEntryTime V x path i hvisit) *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels
          (firstExactLevelEntryTime V x path i hvisit) := by
  exact
    multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
      P V hbound p x path labels i hvisit coord
      (firstExactLevelEntryTime V x path i hvisit) le_rfl

end ECRuntime
