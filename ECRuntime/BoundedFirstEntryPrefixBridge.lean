import ECRuntime.BoundedCoupledExactLevelFirstEntrySlices
import ECRuntime.RandomEntryGeometricPattern
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 41: fixed first-entry slices meet the pre-entry prefix interface

Stage 26 fix 40 fix 1 is compiler verified warning-free.  It partitions the bounded
coupled exact-level entry event into disjoint slices indexed by the unique actual
first-entry time.  The pre-entry freshness and coordinate-marginalization theorems from
fixes 33--37, however, are stated for total Nat-indexed state and label streams and use
`firstExactLevelEntryTime`.

This module supplies the finite-to-stream bridge needed to apply those results to one
concrete fix-40 slice.  A finite state trajectory is reused through the absolute-time
view introduced in fix 40; a finite vector-label trajectory is embedded into a total
transition-indexed stream by padding with the all-false vector outside the finite
horizon.  If a bounded state path first visits exact level `i+1` at time `s`, then the
`firstExactLevelEntryTime` of its total stream is exactly `s`.

Consequently the already verified exhaustive pre-entry coordinate marginalization can
be specialized directly to that fixed slice.  The final theorem carries the
`r`-failures-then-success continuation and produces the exact geometric factor
`(1-p_i)^r p_i` for the concrete bounded first-entry path.

This stage intentionally stops one interface short of identifying the whole fix-40
finite coupled slice mass.  The next bridge only needs to relate the recursive finite
coupled path weight to the prefix-product representation on the first `s` transitions;
all stopping-time alignment and inactive-coordinate marginalization are handled here.
-/

/-- Embed a finite vector-label path into a total transition-indexed stream.  Values
outside the finite horizon are padded with the all-false vector. -/
def finiteMultiLevelLabelStream
    {m T : Nat}
    (labels : FiniteTrajectory (Fin m -> Bool) T) : Nat -> (Fin m -> Bool) :=
  fun t => if ht : t < T then labels ⟨t, ht⟩ else fun _ => false

@[simp] theorem finiteMultiLevelLabelStream_apply_of_lt
    {m T : Nat}
    (labels : FiniteTrajectory (Fin m -> Bool) T)
    (t : Nat) (ht : t < T) :
    finiteMultiLevelLabelStream labels t = labels ⟨t, ht⟩ := by
  simp [finiteMultiLevelLabelStream, ht]

/-- The fix-40 absolute-time finite state view is exactly the state sequence seen by
`transitionTrajectoryState` when reused as the total path stream. -/
@[simp] theorem transitionTrajectoryState_finiteTrajectoryAbsoluteState
    {alpha : Type*} {T : Nat}
    (x : alpha) (states : FiniteTrajectory alpha T) (s : Nat) :
    transitionTrajectoryState x (finiteTrajectoryAbsoluteState x states) s =
      finiteTrajectoryAbsoluteState x states s := by
  cases s with
  | zero => simp
  | succ t => rfl

/-- A concrete fix-40 first-entry slice supplies the existence witness required by the
Nat-indexed first-entry interface. -/
theorem finiteFirstEntrySliceVisitWitness
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (states : FiniteTrajectory alpha T) (i : Fin m) (s : Nat)
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i s) :
    Exists fun r : Nat =>
      V (transitionTrajectoryState x
        (finiteTrajectoryAbsoluteState x states) r) = i.val + 1 := by
  refine ⟨s, ?_⟩
  simpa using hfirst.2.1

/-- On a bounded first-entry slice, the generic Nat-indexed first-entry time agrees
exactly with the slice index. -/
theorem firstExactLevelEntryTime_finiteFirstEntrySlice
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (states : FiniteTrajectory alpha T) (i : Fin m) (s : Nat)
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i s) :
    firstExactLevelEntryTime V x
        (finiteTrajectoryAbsoluteState x states) i
        (finiteFirstEntrySliceVisitWitness V x states i s hfirst) = s := by
  let hvisit := finiteFirstEntrySliceVisitWitness V x states i s hfirst
  let entry := firstExactLevelEntryTime V x
    (finiteTrajectoryAbsoluteState x states) i hvisit
  have hentry :
      V (transitionTrajectoryState x
        (finiteTrajectoryAbsoluteState x states) entry) = i.val + 1 := by
    exact firstExactLevelEntryTime_spec V x
      (finiteTrajectoryAbsoluteState x states) i hvisit
  have hs :
      V (transitionTrajectoryState x
        (finiteTrajectoryAbsoluteState x states) s) = i.val + 1 := by
    simpa using hfirst.2.1
  have h_entry_le_s : entry <= s := by
    by_contra hnot
    have hslt : s < entry := by omega
    exact (firstExactLevelEntryTime_minimal V x
      (finiteTrajectoryAbsoluteState x states) i hvisit hslt) hs
  have h_s_le_entry : s <= entry := by
    by_contra hnot
    have helt : entry < s := by omega
    exact hfirst.2.2 entry helt (by simpa using hentry)
  have heq : entry = s := Nat.le_antisymm h_entry_le_s h_s_le_entry
  exact heq

/-- Complete marginalization of inactive coordinate `i` before a concrete bounded
first entry.  This is the fix-35 theorem with the abstract `Nat.find` entry time
rewritten to the actual fix-40 slice index. -/
theorem sum_all_preEntryCoordinatePrefixes_fixedFirstEntrySlice
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
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x
          (finiteTrajectoryAbsoluteState x states)
          (updateLabelCoordinateStream
            (finiteMultiLevelLabelStream labels) i
            (finiteBoolPrefixStream coord)) s.val) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) s.val := by
  let hvisit := finiteFirstEntrySliceVisitWitness V x states i s.val hfirst
  have hentry :
      firstExactLevelEntryTime V x
        (finiteTrajectoryAbsoluteState x states) i hvisit = s.val := by
    exact firstExactLevelEntryTime_finiteFirstEntrySlice
      V x states i s.val hfirst
  have h := sum_all_preEntryCoordinatePrefixes_to_firstEntry
    P V hbound p x
      (finiteTrajectoryAbsoluteState x states)
      (finiteMultiLevelLabelStream labels) i hvisit
  rw [hentry] at h
  exact h

/-- The concrete fixed-slice marginalization can carry any continuation factor that is
independent of the discarded pre-entry coordinate. -/
theorem sum_all_preEntryCoordinatePrefixes_mul_constant_fixedFirstEntrySlice
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (states : FiniteTrajectory alpha T)
    (labels : FiniteTrajectory (Fin m -> Bool) T)
    (i : Fin m) (s : Fin (T + 1))
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i s.val)
    (postMass : Real) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool s.val =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x
          (finiteTrajectoryAbsoluteState x states)
          (updateLabelCoordinateStream
            (finiteMultiLevelLabelStream labels) i
            (finiteBoolPrefixStream coord)) s.val * postMass) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) s.val * postMass := by
  calc
    (Finset.univ.sum fun coord : FiniteTrajectory Bool s.val =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x
          (finiteTrajectoryAbsoluteState x states)
          (updateLabelCoordinateStream
            (finiteMultiLevelLabelStream labels) i
            (finiteBoolPrefixStream coord)) s.val * postMass) =
        (Finset.univ.sum fun coord : FiniteTrajectory Bool s.val =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x
              (finiteTrajectoryAbsoluteState x states)
              (updateLabelCoordinateStream
                (finiteMultiLevelLabelStream labels) i
                (finiteBoolPrefixStream coord)) s.val) * postMass := by
          rw [Finset.sum_mul]
    _ = preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) s.val * postMass := by
      rw [sum_all_preEntryCoordinatePrefixes_fixedFirstEntrySlice
        P V hbound p x states labels i s hfirst]

/-- Fixed-slice geometric continuation.  After summing every possible inactive
coordinate prefix before the concrete first-entry time, the remaining factor is the
coordinate-deleted slice weight times the exact `r`-failures-then-success Bernoulli
mass. -/
theorem sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccess_fixedFirstEntrySlice
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
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x
          (finiteTrajectoryAbsoluteState x states)
          (updateLabelCoordinateStream
            (finiteMultiLevelLabelStream labels) i
            (finiteBoolPrefixStream coord)) s.val *
        bernoulliBoolPrefixWeight (p i)
          (failuresThenSuccessCoordinate r) (r + 1)) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x states)
          (finiteMultiLevelLabelStream labels) s.val *
        ((1 - p i) ^ r * p i) := by
  rw [sum_all_preEntryCoordinatePrefixes_mul_constant_fixedFirstEntrySlice
    P V hbound p x states labels i s hfirst
      (bernoulliBoolPrefixWeight (p i)
        (failuresThenSuccessCoordinate r) (r + 1))]
  rw [bernoulliBoolPrefixWeight_failuresThenSuccess]

end ECRuntime
