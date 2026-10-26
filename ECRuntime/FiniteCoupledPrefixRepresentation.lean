import ECRuntime.BoundedFirstEntryPrefixBridge
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 42 fix 1: recursive finite coupled weights equal prefix products

Stage 26 fix 41 compiled successfully in the pinned Lean 4.32.1 environment; its only
reported diagnostic was the style linter asking that a proposition-valued helper be a
`theorem` rather than a `def`.  That declaration is cleaned in this version.

The substantive remaining interface after fix 41 is representational.  The finite
coupled law used by the bounded first-entry slices is defined recursively through
`finiteLabeledTrajectoryWeight`, whereas the pre-entry freshness and marginalization
results use the explicit product `multiLevelBernoulliCoupledPrefixWeight`.

The first fix-42 build reached the generic product induction and failed only in the
shifted-tail pointwise equality: `simp` could not infer the erased initial-state argument of
`transitionTrajectoryState_shift`.  Fix 42 fix 1 makes those two shift rewrites explicit.

This module proves that these are the same finite object.  First it establishes a
generic stream-to-finite-path product formula for an arbitrary labelled step weight.
It then specializes that identity to the adaptive multi-level coupling and finally to
one concrete first-entry slice, including the coordinate-updated prefixes used in the
fix-41 exhaustive marginalization theorem.

No new probabilistic assumption is introduced.  The results are finite algebraic
identities and require neither stochastic normalization nor exit-probability bounds.
-/

/-- Read the first `T` values of a transition-indexed label stream as a finite label
trajectory.  Unlike `transitionTrajectoryTail` for states, labels are already indexed
by transition number, so no `+1` shift is used here. -/
def transitionLabelTrajectory {beta : Type*}
    (T : Nat) (labels : Nat -> beta) : FiniteTrajectory beta T :=
  fun j => labels j.val

@[simp] theorem transitionLabelTrajectory_apply
    {beta : Type*} (T : Nat) (labels : Nat -> beta) (j : Fin T) :
    transitionLabelTrajectory T labels j = labels j.val := by
  rfl

/-- Tailing a finite label trajectory extracted from a stream is the same as extracting
from the one-step-shifted label stream. -/
theorem Fin_tail_transitionLabelTrajectory
    {beta : Type*} (T : Nat) (labels : Nat -> beta) :
    Fin.tail (transitionLabelTrajectory (T + 1) labels) =
      transitionLabelTrajectory T (fun t => labels (t + 1)) := by
  funext j
  rfl

/-- Tailing a zipped finite state/label path tails both components. -/
theorem Fin_tail_zipFiniteTrajectories
    {alpha beta : Type*} {T : Nat}
    (states : FiniteTrajectory alpha (T + 1))
    (labels : FiniteTrajectory beta (T + 1)) :
    Fin.tail (zipFiniteTrajectories states labels) =
      zipFiniteTrajectories (Fin.tail states) (Fin.tail labels) := by
  funext j
  rfl

/-- Generic representation theorem: the recursive labelled finite-path weight of the
first `T` coordinates of complete state/label streams is exactly the product of the
one-step weights over transition indices `0, ..., T-1`. -/
theorem finiteLabeledTrajectoryWeight_stream_eq_prefixProduct
    {alpha beta : Type*}
    (J : alpha -> alpha -> beta -> Real) :
    forall T (x : alpha) (path : Nat -> alpha) (labels : Nat -> beta),
      finiteLabeledTrajectoryWeight J T x
          (zipFiniteTrajectories
            (transitionTrajectoryTail T path)
            (transitionLabelTrajectory T labels)) =
        ∏ t ∈ Finset.range T,
          J (transitionTrajectoryState x path t)
            (transitionTrajectoryState x path (t + 1))
            (labels t) := by
  intro T
  induction T with
  | zero =>
      intro x path labels
      simp [finiteLabeledTrajectoryWeight]
  | succ T ih =>
      intro x path labels
      have htail :
          Fin.tail
              (zipFiniteTrajectories
                (transitionTrajectoryTail (T + 1) path)
                (transitionLabelTrajectory (T + 1) labels)) =
            zipFiniteTrajectories
              (transitionTrajectoryTail T (transitionTrajectoryShift path))
              (transitionLabelTrajectory T (fun t => labels (t + 1))) := by
        rw [Fin_tail_zipFiniteTrajectories]
        rw [Fin_tail_transitionTrajectoryTail]
        rw [Fin_tail_transitionLabelTrajectory]
      change
        J x (path 1) (labels 0) *
            finiteLabeledTrajectoryWeight J T (path 1)
              (Fin.tail
                (zipFiniteTrajectories
                  (transitionTrajectoryTail (T + 1) path)
                  (transitionLabelTrajectory (T + 1) labels))) =
          ∏ t ∈ Finset.range (T + 1),
            J (transitionTrajectoryState x path t)
              (transitionTrajectoryState x path (t + 1))
              (labels t)
      rw [htail]
      rw [ih (path 1) (transitionTrajectoryShift path)
        (fun t => labels (t + 1))]
      let f : Nat -> Real := fun t =>
        J (transitionTrajectoryState x path t)
          (transitionTrajectoryState x path (t + 1))
          (labels t)
      have hshift :
          (∏ t ∈ Finset.range T,
            J
              (transitionTrajectoryState (path 1)
                (transitionTrajectoryShift path) t)
              (transitionTrajectoryState (path 1)
                (transitionTrajectoryShift path) (t + 1))
              (labels (t + 1))) =
            ∏ t ∈ Finset.range T, f (t + 1) := by
        apply Finset.prod_congr rfl
        intro t _ht
        rw [transitionTrajectoryState_shift x path t]
        rw [transitionTrajectoryState_shift x path (t + 1)]
      rw [hshift]
      change f 0 * (∏ t ∈ Finset.range T, f (t + 1)) =
        ∏ t ∈ Finset.range (T + 1), f t
      calc
        f 0 * (∏ t ∈ Finset.range T, f (t + 1)) =
            (∏ t ∈ Finset.range T, f (t + 1)) * f 0 := by
              rw [mul_comm]
        _ = ∏ t ∈ Finset.range (T + 1), f t := by
          exact (Finset.prod_range_succ' f T).symm

/-- Reading the first `T` states back from the fix-40 finite absolute-state stream
recovers the original finite state trajectory. -/
theorem transitionTrajectoryTail_finiteTrajectoryAbsoluteState
    {alpha : Type*} {T : Nat}
    (x : alpha) (states : FiniteTrajectory alpha T) :
    transitionTrajectoryTail T (finiteTrajectoryAbsoluteState x states) = states := by
  funext j
  unfold transitionTrajectoryTail
  rw [finiteTrajectoryAbsoluteState_succ_of_lt x states j.val j.isLt]

/-- Reading the first `T` labels back from the fix-41 total label stream recovers the
original finite label trajectory. -/
theorem transitionLabelTrajectory_finiteMultiLevelLabelStream
    {m T : Nat}
    (labels : FiniteTrajectory (Fin m -> Bool) T) :
    transitionLabelTrajectory T (finiteMultiLevelLabelStream labels) = labels := by
  funext j
  exact finiteMultiLevelLabelStream_apply_of_lt labels j.val j.isLt

/-- The recursive adaptive finite coupled path weight is exactly the explicit prefix
product on the finite absolute-state and total-label streams. -/
theorem finiteMultiLevelBernoulliCoupledWeight_zip_eq_prefixWeight
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (states : FiniteTrajectory alpha T)
    (labels : FiniteTrajectory (Fin m -> Bool) T) :
    finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
        (zipFiniteTrajectories states labels) =
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) T := by
  have h := finiteLabeledTrajectoryWeight_stream_eq_prefixProduct
    (multiLevelBernoulliCoupledStepWeight P V hbound p)
    T x (finiteTrajectoryAbsoluteState x states)
      (finiteMultiLevelLabelStream labels)
  rw [transitionTrajectoryTail_finiteTrajectoryAbsoluteState x states] at h
  rw [transitionLabelTrajectory_finiteMultiLevelLabelStream labels] at h
  simpa [finiteMultiLevelBernoulliCoupledWeight,
    multiLevelBernoulliCoupledPrefixWeight] using h

/-- Recursive finite coupled weight of an arbitrary stream prefix.  This is the form
needed when coordinate `i` has been replaced by one candidate pre-entry Boolean
prefix. -/
theorem finiteMultiLevelBernoulliCoupledWeight_streamPrefix_eq_prefixWeight
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (T : Nat) (x : alpha)
    (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool)) :
    finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
        (zipFiniteTrajectories
          (transitionTrajectoryTail T path)
          (transitionLabelTrajectory T labels)) =
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path labels T := by
  have h := finiteLabeledTrajectoryWeight_stream_eq_prefixProduct
    (multiLevelBernoulliCoupledStepWeight P V hbound p)
    T x path labels
  simpa [finiteMultiLevelBernoulliCoupledWeight,
    multiLevelBernoulliCoupledPrefixWeight] using h

/-- On one concrete first-entry slice, the exhaustive inactive-coordinate
marginalization from fix 41 can be written entirely using the recursive finite coupled
path weight. -/
theorem sum_all_preEntryCoordinateFiniteWeights_fixedFirstEntrySlice
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (states : FiniteTrajectory alpha T)
    (labels : FiniteTrajectory (Fin m -> Bool) T)
    (i : Fin m) (s : Fin (T + 1))
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i s.val) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool s.val =>
      finiteMultiLevelBernoulliCoupledWeight P V hbound p s.val x
        (zipFiniteTrajectories
          (transitionTrajectoryTail s.val
            (finiteTrajectoryAbsoluteState x states))
          (transitionLabelTrajectory s.val
            (updateLabelCoordinateStream
              (finiteMultiLevelLabelStream labels) i
              (finiteBoolPrefixStream coord))))) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) s.val := by
  simp_rw [finiteMultiLevelBernoulliCoupledWeight_streamPrefix_eq_prefixWeight]
  exact sum_all_preEntryCoordinatePrefixes_fixedFirstEntrySlice
    P V hbound p x states labels i s hfirst

/-- The recursive finite-weight formulation also carries the exact geometric
`r`-failures-then-success continuation. -/
theorem sum_all_preEntryCoordinateFiniteWeights_mul_failuresThenSuccess_fixedFirstEntrySlice
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (states : FiniteTrajectory alpha T)
    (labels : FiniteTrajectory (Fin m -> Bool) T)
    (i : Fin m) (s : Fin (T + 1))
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i s.val)
    (r : Nat) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool s.val =>
      finiteMultiLevelBernoulliCoupledWeight P V hbound p s.val x
        (zipFiniteTrajectories
          (transitionTrajectoryTail s.val
            (finiteTrajectoryAbsoluteState x states))
          (transitionLabelTrajectory s.val
            (updateLabelCoordinateStream
              (finiteMultiLevelLabelStream labels) i
              (finiteBoolPrefixStream coord)))) *
        bernoulliBoolPrefixWeight (p i)
          (failuresThenSuccessCoordinate r) (r + 1)) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) s.val *
        ((1 - p i) ^ r * p i) := by
  simp_rw [finiteMultiLevelBernoulliCoupledWeight_streamPrefix_eq_prefixWeight]
  exact
    sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccess_fixedFirstEntrySlice
      P V hbound p x states labels i s hfirst r

end ECRuntime
