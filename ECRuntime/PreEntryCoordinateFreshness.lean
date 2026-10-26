import ECRuntime.HistoryDependentWaiting
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 32: pre-entry inactive-coordinate freshness

Stage 26 fix 31 fix 1 compiler-verifies the pathwise random-entry residence bound:
starting the comparison clock at the actual first visit of exact level `i+1`, the first
success of Bernoulli coordinate `i` bounds that level's residence length on positive
coupled-step support.

The remaining probabilistic step must not use an unjustified generic "i.i.d. after a
random shift" principle: the first-entry time is history dependent.  What makes the
present coupling usable is more specific.  Strictly before level `i+1` is first entered,
coordinate `i` is *inactive*.  Hence its Bernoulli factor is independent of the real
transition and of all other coordinates at that step.

This module exposes that fact locally.  It factors an inactive coordinate from both the
fixed-active vector step and the global adaptive step, proves that the remaining factor
is invariant under changing only that coordinate, and specializes the result to every
transition strictly before the actual first exact-level entry.  These identities are the
finite-step ingredient for the next history induction establishing freshness at the
stopping entry time.
-/

/-- Product of a fixed-active vector step over all coordinates except `i`.

The genuinely coupled scalar factor is retained when its active coordinate occurs in the
complement; all other coordinates retain their ordinary Bernoulli factors. -/
noncomputable def levelBernoulliVectorCoupledStepComplementExcept
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (active i : Fin m)
    (x y : α) (bits : Fin m → Bool) : ℝ :=
  ∏ j ∈ ({i}ᶜ : Finset (Fin m)),
    if j = active then
      levelBernoulliCoupledStepWeight P level (p active) x y (bits j)
    else
      bernoulliBoolWeight (p j) (bits j)

/-- If coordinate `i` is not the active coordinate, the full fixed-active vector step
factors into the ordinary Bernoulli weight of `i` and a factor involving all remaining
coordinates. -/
theorem levelBernoulliVectorCoupledStepWeight_eq_inactiveCoordinate_mul_complement
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (active i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hia : i ≠ active) :
    levelBernoulliVectorCoupledStepWeight P level p active x y bits =
      bernoulliBoolWeight (p i) (bits i) *
        levelBernoulliVectorCoupledStepComplementExcept
          P level p active i x y bits := by
  classical
  unfold levelBernoulliVectorCoupledStepWeight
    levelBernoulliVectorCoupledStepComplementExcept
  rw [Fintype.prod_eq_mul_prod_compl i]
  rw [if_neg hia]

/-- Changing coordinate `i` does not change the complement product that omits `i`. -/
theorem levelBernoulliVectorCoupledStepComplementExcept_update_self
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (active i : Fin m)
    (x y : α) (bits : Fin m → Bool) (b : Bool) :
    levelBernoulliVectorCoupledStepComplementExcept
        P level p active i x y (Function.update bits i b) =
      levelBernoulliVectorCoupledStepComplementExcept
        P level p active i x y bits := by
  classical
  unfold levelBernoulliVectorCoupledStepComplementExcept
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    simpa using hj
  simp [hji]

/-- Changing coordinate `i` does not change the ordinary product-Bernoulli complement
that omits `i`. -/
theorem bernoulliLevelVectorComplementWeight_update_self
    {m : ℕ} (p : Fin m → ℝ) (i : Fin m)
    (bits : Fin m → Bool) (b : Bool) :
    bernoulliLevelVectorComplementWeight p i (Function.update bits i b) =
      bernoulliLevelVectorComplementWeight p i bits := by
  classical
  unfold bernoulliLevelVectorComplementWeight
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    simpa using hj
  simp [hji]

/-- The global adaptive step with coordinate `i` removed.

At potential zero this is the original transition factor times the product-Bernoulli
complement.  At positive potential it is the complement of the vector step whose active
coordinate is selected by the current potential. -/
noncomputable def multiLevelBernoulliInactiveCoordinateComplementWeight
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool) : ℝ := by
  classical
  by_cases hx : V x = 0
  · exact P x y * bernoulliLevelVectorComplementWeight p i bits
  · let active : Fin m := activePositivePotentialLevelIndex V hbound x hx
    exact levelBernoulliVectorCoupledStepComplementExcept
      P (exactPositivePotentialLevel V active) p active i x y bits

/-- The global inactive-coordinate complement is insensitive to the omitted bit. -/
theorem multiLevelBernoulliInactiveCoordinateComplementWeight_update_self
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool) (b : Bool) :
    multiLevelBernoulliInactiveCoordinateComplementWeight
        P V hbound p i x y (Function.update bits i b) =
      multiLevelBernoulliInactiveCoordinateComplementWeight
        P V hbound p i x y bits := by
  classical
  by_cases hx : V x = 0
  · simp [multiLevelBernoulliInactiveCoordinateComplementWeight, hx,
      bernoulliLevelVectorComplementWeight_update_self]
  · let active : Fin m := activePositivePotentialLevelIndex V hbound x hx
    simp [multiLevelBernoulliInactiveCoordinateComplementWeight, hx,
      levelBernoulliVectorCoupledStepComplementExcept_update_self]

/-- Whenever the current potential is not `i+1`, coordinate `i` is inactive and factors
from the global adaptive coupled step as an ordinary Bernoulli factor. -/
theorem multiLevelBernoulliCoupledStepWeight_eq_inactiveCoordinate_mul_complement
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hi : V x ≠ i.val + 1) :
    multiLevelBernoulliCoupledStepWeight P V hbound p x y bits =
      bernoulliBoolWeight (p i) (bits i) *
        multiLevelBernoulliInactiveCoordinateComplementWeight
          P V hbound p i x y bits := by
  classical
  by_cases hx : V x = 0
  · rw [show multiLevelBernoulliCoupledStepWeight P V hbound p x y bits =
        P x y * bernoulliLevelVectorWeight p bits by
        simp [multiLevelBernoulliCoupledStepWeight, hx]]
    rw [bernoulliLevelVectorWeight_eq_active_mul_complement p i bits]
    rw [show multiLevelBernoulliInactiveCoordinateComplementWeight
          P V hbound p i x y bits =
        P x y * bernoulliLevelVectorComplementWeight p i bits by
        simp [multiLevelBernoulliInactiveCoordinateComplementWeight, hx]]
    ring
  · let active : Fin m := activePositivePotentialLevelIndex V hbound x hx
    have hactiveVal : V x = active.val + 1 := by
      simpa [active] using activePositivePotentialLevelIndex_value V hbound x hx
    have hia : i ≠ active := by
      intro hieq
      apply hi
      calc
        V x = active.val + 1 := hactiveVal
        _ = i.val + 1 := by rw [← hieq]
    rw [show multiLevelBernoulliCoupledStepWeight P V hbound p x y bits =
        levelBernoulliVectorCoupledStepWeight
          P (exactPositivePotentialLevel V active) p active x y bits by
        simp [multiLevelBernoulliCoupledStepWeight, hx, active]]
    rw [show multiLevelBernoulliInactiveCoordinateComplementWeight
          P V hbound p i x y bits =
        levelBernoulliVectorCoupledStepComplementExcept
          P (exactPositivePotentialLevel V active) p active i x y bits by
        simp [multiLevelBernoulliInactiveCoordinateComplementWeight, hx, active]]
    exact levelBernoulliVectorCoupledStepWeight_eq_inactiveCoordinate_mul_complement
      P (exactPositivePotentialLevel V active) p active i x y bits hia

/-- Updating an inactive coordinate to an arbitrary Boolean value changes the coupled
step weight only through that coordinate's scalar Bernoulli factor. -/
theorem multiLevelBernoulliCoupledStepWeight_update_inactiveCoordinate
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hi : V x ≠ i.val + 1) (b : Bool) :
    multiLevelBernoulliCoupledStepWeight
        P V hbound p x y (Function.update bits i b) =
      bernoulliBoolWeight (p i) b *
        multiLevelBernoulliInactiveCoordinateComplementWeight
          P V hbound p i x y bits := by
  rw [multiLevelBernoulliCoupledStepWeight_eq_inactiveCoordinate_mul_complement
    P V hbound p i x y (Function.update bits i b) hi]
  rw [multiLevelBernoulliInactiveCoordinateComplementWeight_update_self
    P V hbound p i x y bits b]
  simp

/-- Summing the two possible values of an inactive coordinate removes that coordinate
and leaves exactly the complement factor. -/
theorem sum_multiLevelBernoulliCoupledStepWeight_update_inactiveCoordinate
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool)
    (hi : V x ≠ i.val + 1) :
    (∑ b : Bool,
      multiLevelBernoulliCoupledStepWeight
        P V hbound p x y (Function.update bits i b)) =
      multiLevelBernoulliInactiveCoordinateComplementWeight
        P V hbound p i x y bits := by
  simp_rw [multiLevelBernoulliCoupledStepWeight_update_inactiveCoordinate
    P V hbound p i x y bits hi]
  rw [← Finset.sum_mul]
  rw [sum_bernoulliBoolWeight]
  ring

/-- Before the actual first entry into exact level `i+1`, coordinate `i` factors from
every adaptive transition as an ordinary Bernoulli variable. -/
theorem multiLevelBernoulliCoupledStepWeight_eq_inactiveCoordinate_mul_before_firstEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ s,
      V (transitionTrajectoryState x path s) = i.val + 1)
    {t : ℕ} (ht : t < firstExactLevelEntryTime V x path i hvisit)
    (y : α) (bits : Fin m → Bool) :
    multiLevelBernoulliCoupledStepWeight
        P V hbound p (transitionTrajectoryState x path t) y bits =
      bernoulliBoolWeight (p i) (bits i) *
        multiLevelBernoulliInactiveCoordinateComplementWeight
          P V hbound p i (transitionTrajectoryState x path t) y bits := by
  exact multiLevelBernoulliCoupledStepWeight_eq_inactiveCoordinate_mul_complement
    P V hbound p i (transitionTrajectoryState x path t) y bits
    (firstExactLevelEntryTime_minimal V x path i hvisit ht)

/-- Update form of the pre-entry freshness identity.  This is the convenient statement
for the next finite-history induction because the complement is shared by both values
of coordinate `i`. -/
theorem multiLevelBernoulliCoupledStepWeight_update_before_firstEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ s,
      V (transitionTrajectoryState x path s) = i.val + 1)
    {t : ℕ} (ht : t < firstExactLevelEntryTime V x path i hvisit)
    (y : α) (bits : Fin m → Bool) (b : Bool) :
    multiLevelBernoulliCoupledStepWeight
        P V hbound p (transitionTrajectoryState x path t) y
          (Function.update bits i b) =
      bernoulliBoolWeight (p i) b *
        multiLevelBernoulliInactiveCoordinateComplementWeight
          P V hbound p i (transitionTrajectoryState x path t) y bits := by
  exact multiLevelBernoulliCoupledStepWeight_update_inactiveCoordinate
    P V hbound p i (transitionTrajectoryState x path t) y bits
    (firstExactLevelEntryTime_minimal V x path i hvisit ht) b

end ECRuntime
