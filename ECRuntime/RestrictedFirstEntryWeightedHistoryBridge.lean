import ECRuntime.RestrictedFirstEntryDeletedCoordinateMass
import ECRuntime.WeightedFirstEntryGeometricFactorization
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 59: fixed-time weighted-history bridge

Stage 26 fix 58 fix 1 is compiler verified warning-free.  For every fixed first-entry
horizon `T`, it identifies the genuine adaptive restricted exact-time mass with
`restrictedTerminalFirstEntryComplementMass`, a finite sum over deleted-coordinate
prefixes.

The generic geometric peeling theorem from fix 53 is phrased instead through
`weightedFirstEntryHistoryComplementMass`.  This file supplies the exact finite bridge
between those two interfaces.

The history type is the finite subtype of deleted-coordinate prefixes whose state
component first visits exact level `i+1` at terminal time `T`.  The outer coefficient is
the indicator of the finite deleted-coordinate restriction `C`.  The bounded-to-stream
bridge from fix 41 identifies the generic `firstExactLevelEntryTime` of every such
history with `T`, so the fix-53 summand is definitionally the same pre-entry complement
prefix weight used by fix 58.

The resulting endpoint says that, at fixed `T`, the genuine infinite restricted
exact-entry slice is exactly the real/`ofReal` mass of a canonical instance of
`weightedFirstEntryHistoryComplementMass`.

This intentionally does not yet identify the full eventual-entry branch with one
finite history family.  Exact entry can occur at arbitrarily large times, so the next
stage should sum these fixed-time weighted masses using the fix-56 `tsum`
decomposition and lift the one-coordinate peeling identity to that countable family.
-/

/-- Canonical finite history type for deleted-coordinate prefixes that first enter
exact level `i+1` precisely at terminal time `T`. -/
abbrev DeletedCoordinateTerminalFirstEntryHistory
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :=
  {path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T //
    finiteTrajectoryFirstVisitsExactLevelAt
      V x (finiteCoupledStateProjection path) i T}

/-- State stream attached to a canonical fixed-time deleted-coordinate history. -/
def deletedCoordinateTerminalFirstEntryStateStream
    {alpha : Type*} {m T : Nat}
    (x : alpha) (i : Fin m)
    {V : alpha -> Nat}
    (a : DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i) : Nat -> alpha :=
  finiteTrajectoryAbsoluteState x (finiteCoupledStateProjection a.1)

/-- Full-vector representative stream attached to a canonical fixed-time
 deleted-coordinate history.  Coordinate `i` is represented by `false`; the fix-53
 complement weight ignores that coordinate before entry. -/
def deletedCoordinateTerminalFirstEntryLabelStream
    {alpha : Type*} {m T : Nat}
    {V : alpha -> Nat} {x : alpha} (i : Fin m)
    (a : DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i) : Nat -> (Fin m -> Bool) :=
  finiteInactiveCoordinateFullLabelStream (finiteCoupledLabelProjection a.1)

/-- Every canonical fixed-time history supplies the visit witness required by the
Nat-indexed fix-53 interface. -/
theorem deletedCoordinateTerminalFirstEntryVisitWitness
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (a : DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i) :
    Exists fun s : Nat =>
      V (transitionTrajectoryState x
        (deletedCoordinateTerminalFirstEntryStateStream x i a) s) = i.val + 1 :=
  finiteFirstEntrySliceVisitWitness
    V x (finiteCoupledStateProjection a.1) i T a.2

/-- The generic first-entry time of a canonical terminal history is exactly `T`. -/
@[simp] theorem firstExactLevelEntryTime_deletedCoordinateTerminalFirstEntryHistory
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (a : DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i) :
    firstExactLevelEntryTime V x
        (deletedCoordinateTerminalFirstEntryStateStream x i a) i
        (deletedCoordinateTerminalFirstEntryVisitWitness V x i a) = T := by
  exact firstExactLevelEntryTime_finiteFirstEntrySlice
    V x (finiteCoupledStateProjection a.1) i T a.2

/-- Indicator weight carrying the finite deleted-coordinate outer restriction into the
fix-53 weighted-history interface. -/
noncomputable def deletedCoordinateTerminalFirstEntryRestrictionWeight
    {alpha : Type*} {m T : Nat}
    {V : alpha -> Nat} {x : alpha} {i : Fin m}
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (a : DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i) : Real := by
  classical
  exact if a.1 ∈ C then 1 else 0

/-- Canonical finite subtype sum underlying the fixed-time weighted-history mass.
It is named so the arbitrary terminal-entry subtype can remain only `Finite` in theorem
statements; a concrete `Fintype` enumeration is chosen locally. -/
noncomputable def restrictedTerminalFirstEntryHistorySubtypeMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) : Real := by
  classical
  let beta := DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i
  letI : Fintype beta := Fintype.ofFinite beta
  exact ∑ a : beta,
    if a.1 ∈ C then
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x
            (finiteCoupledStateProjection a.1))
          (finiteInactiveCoordinateFullLabelStream
            (finiteCoupledLabelProjection a.1)) T
    else 0

/-- Canonical fix-53 weighted-history mass for one exact first-entry time. -/
noncomputable def restrictedTerminalFirstEntryWeightedHistoryMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) : Real := by
  classical
  let beta := DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i
  letI : Fintype beta := Fintype.ofFinite beta
  exact weightedFirstEntryHistoryComplementMass
    P V hbound p x
      (fun a : beta => deletedCoordinateTerminalFirstEntryStateStream x i a)
      (fun a : beta => deletedCoordinateTerminalFirstEntryLabelStream i a)
      i
      (fun a : beta => deletedCoordinateTerminalFirstEntryVisitWitness V x i a)
      (fun a : beta => deletedCoordinateTerminalFirstEntryRestrictionWeight C a)

/-- The fix-58 restricted complement mass is exactly the canonical subtype sum over terminal
first-entry histories. -/
theorem restrictedTerminalFirstEntryComplementMass_eq_historySubtypeMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    restrictedTerminalFirstEntryComplementMass P V hbound p x i C =
      restrictedTerminalFirstEntryHistorySubtypeMass
        P V hbound p x i C := by
  classical
  let beta := DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i
  letI : Fintype beta := Fintype.ofFinite beta
  let s : Finset (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T) :=
    Finset.univ.filter (fun path =>
      finiteTrajectoryFirstVisitsExactLevelAt
        V x (finiteCoupledStateProjection path) i T)
  let f : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T -> Real :=
    fun path =>
      if path ∈ C then
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x
            (finiteTrajectoryAbsoluteState x
              (finiteCoupledStateProjection path))
            (finiteInactiveCoordinateFullLabelStream
              (finiteCoupledLabelProjection path)) T
      else 0
  have hs : forall path,
      path ∈ s ↔
        finiteTrajectoryFirstVisitsExactLevelAt
          V x (finiteCoupledStateProjection path) i T := by
    intro path
    simp [s]
  have hsub :
      s.sum f = Finset.univ.sum (fun a : beta => f a.1) := by
    exact Finset.sum_subtype s hs f
  have hfilter :
      s.sum f =
        restrictedTerminalFirstEntryComplementMass P V hbound p x i C := by
    unfold restrictedTerminalFirstEntryComplementMass
    rw [show s.sum f =
        (Finset.univ :
          Finset (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)).sum
            (fun path =>
              if finiteTrajectoryFirstVisitsExactLevelAt
                  V x (finiteCoupledStateProjection path) i T then
                f path
              else 0) by
      change
        ((Finset.univ :
          Finset (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)).filter
            (fun path => finiteTrajectoryFirstVisitsExactLevelAt
              V x (finiteCoupledStateProjection path) i T)).sum f =
        (Finset.univ :
          Finset (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)).sum
            (fun path =>
              if finiteTrajectoryFirstVisitsExactLevelAt
                  V x (finiteCoupledStateProjection path) i T then
                f path
              else 0)
      exact Finset.sum_filter
        (s := (Finset.univ :
          Finset (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)))
        (fun path => finiteTrajectoryFirstVisitsExactLevelAt
          V x (finiteCoupledStateProjection path) i T) f]
    apply Finset.sum_congr rfl
    intro path _hpath
    by_cases hfirst : finiteTrajectoryFirstVisitsExactLevelAt
        V x (finiteCoupledStateProjection path) i T
    · by_cases hC : path ∈ C
      · simp [f, finiteDeletedCoordinateTerminalFirstEntrySet, hfirst, hC]
      · simp [f, finiteDeletedCoordinateTerminalFirstEntrySet, hfirst, hC]
    · simp [f, finiteDeletedCoordinateTerminalFirstEntrySet, hfirst]
  rw [← hfilter]
  unfold restrictedTerminalFirstEntryHistorySubtypeMass
  change s.sum f = Finset.univ.sum (fun a : beta => f a.1)
  exact hsub

/-- At fixed first-entry time `T`, the canonical fix-53 weighted-history mass is exactly
fix 58's concrete restricted complement mass. -/
theorem restrictedTerminalFirstEntryWeightedHistoryMass_eq_complementMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    restrictedTerminalFirstEntryWeightedHistoryMass
        P V hbound p x i C =
      restrictedTerminalFirstEntryComplementMass
        P V hbound p x i C := by
  classical
  unfold restrictedTerminalFirstEntryWeightedHistoryMass
  let beta := DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i
  letI : Fintype beta := Fintype.ofFinite beta
  unfold weightedFirstEntryHistoryComplementMass
  rw [restrictedTerminalFirstEntryComplementMass_eq_historySubtypeMass
    P V hbound p x i C]
  unfold restrictedTerminalFirstEntryHistorySubtypeMass
  change (Finset.univ.sum fun a : beta =>
      deletedCoordinateTerminalFirstEntryRestrictionWeight C a *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x
            (deletedCoordinateTerminalFirstEntryStateStream x i a)
            (deletedCoordinateTerminalFirstEntryLabelStream i a)
            (firstExactLevelEntryTime V x
              (deletedCoordinateTerminalFirstEntryStateStream x i a) i
              (deletedCoordinateTerminalFirstEntryVisitWitness V x i a))) =
    Finset.univ.sum fun a : beta =>
      if a.1 ∈ C then
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x
            (finiteTrajectoryAbsoluteState x
              (finiteCoupledStateProjection a.1))
            (finiteInactiveCoordinateFullLabelStream
              (finiteCoupledLabelProjection a.1)) T
      else 0
  apply Finset.sum_congr rfl
  intro a _ha
  rw [firstExactLevelEntryTime_deletedCoordinateTerminalFirstEntryHistory
    V x i a]
  by_cases hC : a.1 ∈ C
  · simp [deletedCoordinateTerminalFirstEntryRestrictionWeight, hC,
      deletedCoordinateTerminalFirstEntryStateStream,
      deletedCoordinateTerminalFirstEntryLabelStream]
  · simp [deletedCoordinateTerminalFirstEntryRestrictionWeight, hC]

/-- Fixed-time infinite-path mass in the canonical fix-53 weighted-history form. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_eq_weightedHistory
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i C ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T) =
      ENNReal.ofReal
        (restrictedTerminalFirstEntryWeightedHistoryMass
          P V hbound p x i C) := by
  rw [restrictedTerminalFirstEntryWeightedHistoryMass_eq_complementMass
    P V hbound p x i C]
  exact
    adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_eq_ofReal
      P hP V hbound p hp hp1 hexit x i C

/-- Real-mass form of the fixed-time weighted-history identification. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_toReal_eq_weightedHistory
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i C ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T)).toReal =
      restrictedTerminalFirstEntryWeightedHistoryMass
        P V hbound p x i C := by
  rw [restrictedTerminalFirstEntryWeightedHistoryMass_eq_complementMass
    P V hbound p x i C]
  exact
    adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_toReal
      P hP V hbound p hp hp1 hexit x i C

end ECRuntime
