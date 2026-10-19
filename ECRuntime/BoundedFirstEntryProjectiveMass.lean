import ECRuntime.TerminalFirstEntryComplementMass
import ECRuntime.FiniteTrajectoryConsistency
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 44: projective bounded first-entry complement mass

Stage 26 fix 43 is compiler verified warning-free.  It identifies the
coordinate-deleted pre-entry complement mass with the concrete exact-level
first-entry slice when the first entry occurs at the terminal time of the finite
prefix.

The remaining bounded-horizon bookkeeping is projective consistency.  A first-entry
statement at absolute time `s` depends only on the first `s` transitions.  Therefore
extending the finite state law beyond time `s` cannot change the mass of that slice
when the transition matrix is stochastic.

This file proves that fact first for one extra transition by using the already verified
observable form of finite-trajectory projective consistency.  An induction on the
horizon then identifies every bounded first-entry slice with the terminal complement
mass at its own entry time.  Summing the disjoint slices completes the bounded mass
identification:

    sum_{s <= T} terminalFirstEntryComplementMass(s)
      = boundedExactLevelEntryMass(T)
      = boundedCoupledExactLevelEntryMass(T).

Thus, after this stage, the finite first-entry coefficient is no longer abstract: it is
an actual bounded entry-event mass.  The next stage can pass from these bounded masses
to the random-entry / skipped-level alternative and assemble the geometric comparison
variables.
-/

/-- Forgetting the final stored state preserves every absolute state at times up to the
shorter horizon. -/
theorem finiteTrajectoryAbsoluteState_init_of_le
    {alpha : Type*} {T : Nat}
    (x : alpha) (path : FiniteTrajectory alpha (T + 1))
    (r : Nat) (hr : r <= T) :
    finiteTrajectoryAbsoluteState x (Fin.init path) r =
      finiteTrajectoryAbsoluteState x path r := by
  cases r with
  | zero =>
      simp
  | succ t =>
      have htT : t < T := by omega
      have htT1 : t < T + 1 := by omega
      rw [finiteTrajectoryAbsoluteState_succ_of_lt x (Fin.init path) t htT]
      rw [finiteTrajectoryAbsoluteState_succ_of_lt x path t htT1]
      apply congrArg path
      apply Fin.ext
      rfl

/-- A first-entry event at a time belonging to the shorter horizon is unchanged when
one final state is forgotten. -/
theorem finiteTrajectoryFirstVisitsExactLevelAt_init_iff
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : FiniteTrajectory alpha (T + 1)) (i : Fin m)
    (s : Fin (T + 1)) :
    finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val <->
      finiteTrajectoryFirstVisitsExactLevelAt V x (Fin.init path) i s.val := by
  have hsT : s.val <= T := by omega
  constructor
  · intro hfirst
    refine ⟨hsT, ?_, ?_⟩
    · rw [finiteTrajectoryAbsoluteState_init_of_le x path s.val hsT]
      exact hfirst.2.1
    · intro r hr
      have hrT : r <= T := by omega
      rw [finiteTrajectoryAbsoluteState_init_of_le x path r hrT]
      exact hfirst.2.2 r hr
  · intro hfirst
    refine ⟨by omega, ?_, ?_⟩
    · rw [← finiteTrajectoryAbsoluteState_init_of_le x path s.val hsT]
      exact hfirst.2.1
    · intro r hr
      have hrT : r <= T := by omega
      rw [← finiteTrajectoryAbsoluteState_init_of_le x path r hrT]
      exact hfirst.2.2 r hr

/-- One-step projective consistency of an exact first-entry slice.  Extending the
finite trajectory horizon by one transition leaves every pre-existing first-entry
slice unchanged. -/
theorem boundedExactLevelFirstEntrySliceMass_succ
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (s : Fin (T + 1)) :
    boundedExactLevelFirstEntrySliceMass (T := T + 1) P V x i
        ⟨s.val, by omega⟩ =
      boundedExactLevelFirstEntrySliceMass (T := T) P V x i s := by
  classical
  unfold boundedExactLevelFirstEntrySliceMass
  have hproj := finiteTrajectoryWeight_init_expectation P hP T x
    (fun pref : FiniteTrajectory alpha T =>
      if finiteTrajectoryFirstVisitsExactLevelAt V x pref i s.val then 1 else 0)
  calc
    (∑ path : FiniteTrajectory alpha (T + 1),
        if finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val
        then finiteTrajectoryWeight P (T + 1) x path else 0) =
        ∑ path : FiniteTrajectory alpha (T + 1),
          finiteTrajectoryWeight P (T + 1) x path *
            (if finiteTrajectoryFirstVisitsExactLevelAt
                V x (Fin.init path) i s.val then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      have hevent := finiteTrajectoryFirstVisitsExactLevelAt_init_iff V x path i s
      by_cases hshort :
          finiteTrajectoryFirstVisitsExactLevelAt V x (Fin.init path) i s.val
      · have hlong := hevent.mpr hshort
        simp [hshort, hlong]
      · have hlong :
          ¬ finiteTrajectoryFirstVisitsExactLevelAt V x path i s.val := by
          intro h
          exact hshort (hevent.mp h)
        simp [hshort, hlong]
    _ = ∑ pref : FiniteTrajectory alpha T,
          finiteTrajectoryWeight P T x pref *
            (if finiteTrajectoryFirstVisitsExactLevelAt V x pref i s.val
              then 1 else 0) := hproj
    _ = ∑ pref : FiniteTrajectory alpha T,
          if finiteTrajectoryFirstVisitsExactLevelAt V x pref i s.val
          then finiteTrajectoryWeight P T x pref else 0 := by
      apply Finset.sum_congr rfl
      intro pref _hpref
      by_cases hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x pref i s.val
      · simp [hfirst]
      · simp [hfirst]

/-- Every bounded first-entry slice is equal to the terminal coordinate-deleted
complement mass at its own first-entry time. -/
theorem boundedExactLevelFirstEntrySliceMass_eq_terminalFirstEntryComplementMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) :
    forall (T : Nat) (s : Fin (T + 1)),
      boundedExactLevelFirstEntrySliceMass (T := T) P V x i s =
        terminalFirstEntryComplementMass P V hbound p x i s.val := by
  intro T
  induction T with
  | zero =>
      intro s
      have hs : s = Fin.last 0 := by
        apply Fin.ext
        omega
      subst s
      exact (terminalFirstEntryComplementMass_eq_stateSliceMass
        P V hbound p x i 0).symm
  | succ T ih =>
      intro s
      by_cases hlast : s.val = T + 1
      · have hs : s = Fin.last (T + 1) := by
          apply Fin.ext
          simpa using hlast
        subst s
        exact (terminalFirstEntryComplementMass_eq_stateSliceMass
          P V hbound p x i (T + 1)).symm
      · have hslt : s.val < T + 1 := by omega
        let s0 : Fin (T + 1) := ⟨s.val, hslt⟩
        have hsLong :
            s = (⟨s0.val, by omega⟩ : Fin ((T + 1) + 1)) := by
          apply Fin.ext
          rfl
        rw [hsLong]
        calc
          boundedExactLevelFirstEntrySliceMass (T := T + 1) P V x i
              ⟨s0.val, by omega⟩ =
              boundedExactLevelFirstEntrySliceMass (T := T) P V x i s0 :=
            boundedExactLevelFirstEntrySliceMass_succ P hP V x i s0
          _ = terminalFirstEntryComplementMass P V hbound p x i s0.val :=
            ih s0
          _ = terminalFirstEntryComplementMass P V hbound p x i s.val := by
            rfl

/-- Summing the coordinate-deleted terminal first-entry masses up to horizon `T`
recovers exactly the concrete bounded state entry mass. -/
theorem sum_terminalFirstEntryComplementMass_eq_boundedExactLevelEntryMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) :
    (∑ s : Fin (T + 1),
      terminalFirstEntryComplementMass P V hbound p x i s.val) =
      boundedExactLevelEntryMass P V x i T := by
  calc
    (∑ s : Fin (T + 1),
        terminalFirstEntryComplementMass P V hbound p x i s.val) =
        ∑ s : Fin (T + 1),
          boundedExactLevelFirstEntrySliceMass P V x i s := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact (boundedExactLevelFirstEntrySliceMass_eq_terminalFirstEntryComplementMass
        P hP V hbound p x i T s).symm
    _ = boundedExactLevelEntryMass P V x i T :=
      sum_boundedExactLevelFirstEntrySliceMass_eq_entryMass P V x i

/-- The same summed terminal complement mass is exactly the bounded adaptive coupled
entry mass.  This is the finite mass-identification endpoint of fixes 37--44. -/
theorem sum_terminalFirstEntryComplementMass_eq_boundedCoupledExactLevelEntryMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) :
    (∑ s : Fin (T + 1),
      terminalFirstEntryComplementMass P V hbound p x i s.val) =
      boundedCoupledExactLevelEntryMass P V hbound p x i T := by
  rw [sum_terminalFirstEntryComplementMass_eq_boundedExactLevelEntryMass
    P hP V hbound p x i]
  exact (boundedCoupledExactLevelEntryMass_eq_boundedExactLevelEntryMass
    P V hbound p x i T).symm

end ECRuntime
