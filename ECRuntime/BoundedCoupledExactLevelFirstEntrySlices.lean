import ECRuntime.BoundedCoupledExactLevelEntryMass
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 40: bounded coupled exact-level first-entry slices

Stage 26 fix 39 is compiler verified warning-free.  It proves that the adaptive
multi-level coupled finite law preserves the bounded exact-level entry event after all
vector-valued comparison labels are marginalized.

The next bridge must expose the actual first-entry time.  This module does so entirely
inside the already normalized finite-horizon semantics.  A helper reads a finite path
at absolute times `0, ..., T`; the initial state occupies time zero and the stored
trajectory coordinates occupy times `1, ..., T`.  We then define the event that an
exact positive level is visited for the first time at one particular absolute time.

Every finite state path that visits the level by horizon `T` has a unique such time.
This partitions the bounded entry mass into disjoint first-entry slices.  For each
slice, exhaustive marginalization of the complete vector-label path recovers the
corresponding state-path slice exactly.  Summing the coupled slices therefore gives the
verified bounded coupled entry mass from fix 39.

This isolates the remaining hard step cleanly: on one fixed first-entry-time slice,
rewrite the coupled path weight into the pre-entry prefix form of fixes 33--37 and sum
out the inactive comparison coordinate before entry.
-/

/-- Read a finite trajectory at an absolute time.  Time zero is the supplied initial
state.  At time `s+1 <= T`, the value is finite-path coordinate `s`.  The value outside
the horizon is set to the initial state only to make the helper total; all public uses
below carry an explicit `s <= T` premise. -/
def finiteTrajectoryAbsoluteState
    {alpha : Type*} {T : Nat}
    (x : alpha) (path : FiniteTrajectory alpha T) (s : Nat) : alpha := by
  by_cases hzero : s = 0
  · exact x
  · by_cases hT : s <= T
    · exact path ⟨s - 1, by omega⟩
    · exact x

@[simp] theorem finiteTrajectoryAbsoluteState_zero
    {alpha : Type*} {T : Nat}
    (x : alpha) (path : FiniteTrajectory alpha T) :
    finiteTrajectoryAbsoluteState x path 0 = x := by
  simp [finiteTrajectoryAbsoluteState]

@[simp] theorem finiteTrajectoryAbsoluteState_succ_of_lt
    {alpha : Type*} {T : Nat}
    (x : alpha) (path : FiniteTrajectory alpha T)
    (t : Nat) (ht : t < T) :
    finiteTrajectoryAbsoluteState x path (t + 1) = path ⟨t, ht⟩ := by
  have hle : t + 1 <= T := by omega
  simp [finiteTrajectoryAbsoluteState, hle]

/-- The fix-38 bounded visit event is equivalent to existence of an absolute visit time
between zero and the horizon. -/
theorem finiteTrajectoryVisitsExactLevel_iff_exists_absoluteTime
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : FiniteTrajectory alpha T) (i : Fin m) :
    finiteTrajectoryVisitsExactLevel V x path i ↔
      Exists fun s : Nat => s <= T /\
        V (finiteTrajectoryAbsoluteState x path s) = i.val + 1 := by
  constructor
  · intro hvisit
    rcases hvisit with hx | hpath
    · exact ⟨0, Nat.zero_le T, by simpa using hx⟩
    · rcases hpath with ⟨t, ht⟩
      refine ⟨t.val + 1, by omega, ?_⟩
      rw [finiteTrajectoryAbsoluteState_succ_of_lt x path t.val t.isLt]
      exact ht
  · rintro ⟨s, hsT, hs⟩
    cases s with
    | zero =>
        left
        simpa using hs
    | succ t =>
        have ht : t < T := by omega
        right
        refine ⟨⟨t, ht⟩, ?_⟩
        rw [finiteTrajectoryAbsoluteState_succ_of_lt x path t ht] at hs
        exact hs

/-- A bounded state trajectory first visits exact positive level `i+1` at absolute
time `s`. -/
def finiteTrajectoryFirstVisitsExactLevelAt
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : FiniteTrajectory alpha T) (i : Fin m) (s : Nat) : Prop :=
  s <= T /\
    V (finiteTrajectoryAbsoluteState x path s) = i.val + 1 /\
      forall r : Nat, r < s ->
        V (finiteTrajectoryAbsoluteState x path r) ≠ i.val + 1

/-- A first-entry-time slice is contained in the bounded entry event. -/
theorem finiteTrajectoryFirstVisitsExactLevelAt_implies_visits
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : FiniteTrajectory alpha T) (i : Fin m) (s : Nat)
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x path i s) :
    finiteTrajectoryVisitsExactLevel V x path i := by
  rw [finiteTrajectoryVisitsExactLevel_iff_exists_absoluteTime V x path i]
  exact ⟨s, hfirst.1, hfirst.2.1⟩

/-- Every bounded entry path has a unique first-entry time in `Fin (T+1)`. -/
theorem existsUnique_finiteTrajectoryFirstVisitsExactLevelAt_of_visits
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : FiniteTrajectory alpha T) (i : Fin m)
    (hvisit : finiteTrajectoryVisitsExactLevel V x path i) :
    ExistsUnique fun s : Fin (T + 1) =>
      finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val := by
  have hex : Exists fun s : Nat => s <= T /\
      V (finiteTrajectoryAbsoluteState x path s) = i.val + 1 :=
    (finiteTrajectoryVisitsExactLevel_iff_exists_absoluteTime V x path i).mp hvisit
  let n : Nat := Nat.find hex
  have hn : n <= T /\
      V (finiteTrajectoryAbsoluteState x path n) = i.val + 1 := Nat.find_spec hex
  let s0 : Fin (T + 1) := ⟨n, by omega⟩
  have hs0 : finiteTrajectoryFirstVisitsExactLevelAt V x path i s0.val := by
    refine ⟨hn.1, hn.2, ?_⟩
    intro r hr hre
    exact Nat.find_min hex hr ⟨by omega, hre⟩
  refine ⟨s0, hs0, ?_⟩
  intro s hs
  apply Fin.ext
  have hnot_lt : ¬ (s.val < s0.val) := by
    intro hlt
    exact hs0.2.2 s.val hlt hs.2.1
  have hnot_gt : ¬ (s0.val < s.val) := by
    intro hlt
    exact hs.2.2 s0.val hlt hs0.2.1
  omega

/-- State-path mass of one bounded first-entry-time slice. -/
noncomputable def boundedExactLevelFirstEntrySliceMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (s : Fin (T + 1)) : Real := by
  classical
  exact Finset.univ.sum fun path : FiniteTrajectory alpha T =>
    if finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val
    then finiteTrajectoryWeight P T x path
    else 0

/-- Adaptive coupled mass of one bounded first-entry-time slice, before marginalizing
any vector-label coordinates. -/
noncomputable def boundedCoupledExactLevelFirstEntrySliceMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (s : Fin (T + 1)) : Real := by
  classical
  exact Finset.univ.sum fun states : FiniteTrajectory alpha T =>
    Finset.univ.sum fun labels : FiniteTrajectory (Fin m -> Bool) T =>
      if finiteTrajectoryFirstVisitsExactLevelAt V x states i s.val
      then finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x (zipFiniteTrajectories states labels)
      else 0

/-- Marginalizing the full vector-label path on one fixed first-entry slice recovers
exactly the corresponding state-path slice. -/
theorem boundedCoupledExactLevelFirstEntrySliceMass_eq_stateSliceMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (s : Fin (T + 1)) :
    boundedCoupledExactLevelFirstEntrySliceMass P V hbound p x i s =
      boundedExactLevelFirstEntrySliceMass P V x i s := by
  classical
  unfold boundedCoupledExactLevelFirstEntrySliceMass
    boundedExactLevelFirstEntrySliceMass
  apply Finset.sum_congr rfl
  intro states _hstates
  by_cases hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i s.val
  · simp only [if_pos hfirst]
    exact finiteMultiLevelBernoulliCoupledWeight_state_marginal
      P V hbound p T x states
  · simp [hfirst]

/-- The disjoint state-path first-entry slices sum exactly to the bounded exact-level
entry mass from fix 38. -/
theorem sum_boundedExactLevelFirstEntrySliceMass_eq_entryMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    (∑ s : Fin (T + 1), boundedExactLevelFirstEntrySliceMass P V x i s) =
      boundedExactLevelEntryMass P V x i T := by
  classical
  unfold boundedExactLevelFirstEntrySliceMass boundedExactLevelEntryMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro path _hpath
  by_cases hvisit : finiteTrajectoryVisitsExactLevel V x path i
  · rcases existsUnique_finiteTrajectoryFirstVisitsExactLevelAt_of_visits
      V x path i hvisit with ⟨s0, hs0, hunique⟩
    have hslice :
        (∑ s : Fin (T + 1),
          if finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val
          then finiteTrajectoryWeight P T x path else 0) =
        finiteTrajectoryWeight P T x path := by
      calc
        (∑ s : Fin (T + 1),
            if finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val
            then finiteTrajectoryWeight P T x path else 0) =
            (if finiteTrajectoryFirstVisitsExactLevelAt V x path i s0.val
              then finiteTrajectoryWeight P T x path else 0) := by
          apply Fintype.sum_eq_single s0
          intro s hne
          rw [if_neg]
          intro hs
          exact hne (hunique s hs)
        _ = finiteTrajectoryWeight P T x path := by simp [hs0]
    simpa [hvisit] using hslice
  · have hslice :
        (∑ s : Fin (T + 1),
          if finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val
          then finiteTrajectoryWeight P T x path else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s _hs
      rw [if_neg]
      intro hfirst
      exact hvisit
        (finiteTrajectoryFirstVisitsExactLevelAt_implies_visits
          V x path i s.val hfirst)
    simpa [hvisit] using hslice

/-- The disjoint coupled first-entry slices sum exactly to the bounded coupled entry
mass from fix 39. -/
theorem sum_boundedCoupledExactLevelFirstEntrySliceMass_eq_entryMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) :
    (∑ s : Fin (T + 1),
      boundedCoupledExactLevelFirstEntrySliceMass P V hbound p x i s) =
      boundedCoupledExactLevelEntryMass P V hbound p x i T := by
  calc
    (∑ s : Fin (T + 1),
        boundedCoupledExactLevelFirstEntrySliceMass P V hbound p x i s) =
        ∑ s : Fin (T + 1), boundedExactLevelFirstEntrySliceMass P V x i s := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact boundedCoupledExactLevelFirstEntrySliceMass_eq_stateSliceMass
        P V hbound p x i s
    _ = boundedExactLevelEntryMass P V x i T :=
      sum_boundedExactLevelFirstEntrySliceMass_eq_entryMass P V x i
    _ = boundedCoupledExactLevelEntryMass P V hbound p x i T := by
      symm
      exact boundedCoupledExactLevelEntryMass_eq_boundedExactLevelEntryMass
        P V hbound p x i T

end ECRuntime
