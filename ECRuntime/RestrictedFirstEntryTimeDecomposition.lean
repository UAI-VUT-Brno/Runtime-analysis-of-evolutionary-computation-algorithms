import ECRuntime.WeightedPermanentSkipIdentification
import ECRuntime.InfiniteAdaptiveCoupledMarginals
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-!
# Stage 26 fix 56: restricted first-entry-time decomposition

Stage 26 fix 55 fix 1 is compiler verified warning-free.  The remaining hypothesis in
`weightedEntrySkipGeometricFailurePatternMass_eq_restrictedRealMass_mul_pattern`
identifies a finite weighted family of eventual-entry histories with the mass of a
genuine restricted eventual-entry event under the infinite adaptive coupled law.

There is an important countability interface between those two descriptions.  The
genuine eventual-entry event is not one finite first-entry family: it is the disjoint
countable union over all possible first-entry times.  Earlier Stage-26 modules already
proved the corresponding state-path decomposition, but fix 55 only pulled the total
event through the state projection.

This module supplies the missing coupled-law layer.  It defines exact first-entry-time
events directly on the adaptive pair-path space, proves that they are measurable and
pairwise disjoint, and shows that their union is exactly the coupled eventual-entry
event from fix 55.  Intersecting with an arbitrary measurable restriction `A` preserves
that disjoint countable decomposition, so the restricted eventual-entry mass is the
`tsum` of the restricted exact-time masses.

For the unrestricted branch, every exact-time coupled mass is also identified with the
already verified `terminalFirstEntryComplementMass`: the event is a finite cylinder,
fix 47 transports it to the finite adaptive coupled law, and fix 48 marginalizes the
finite pair trajectory to its state component.

The next substantive bridge is therefore finite and local.  For each fixed first-entry
time `T`, identify the restricted exact-time mass below with the appropriate weighted
finite-history complement sum.  Summing those slice identities will then discharge the
countable version of the `hentry` obligation without conflating a finite `Fintype`
mixture with an infinite eventual-entry event.
-/

/-- Exact first visit of level `i+1` at absolute time `T`, viewed on the genuine
adaptive pair-path space through its state projection. -/
def adaptiveCoupledFirstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  adaptiveCoupledStatePath ⁻¹'
    transitionTrajectoryFirstExactLevelEntrySet V x i T

/-- Every adaptive coupled exact-first-entry-time event is measurable. -/
theorem measurableSet_adaptiveCoupledFirstExactLevelEntrySet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    MeasurableSet (adaptiveCoupledFirstExactLevelEntrySet V x i T) := by
  unfold adaptiveCoupledFirstExactLevelEntrySet
  exact
    (measurableSet_transitionTrajectoryFirstExactLevelEntrySet V x i T).preimage
      (measurable_adaptiveCoupledStatePath (alpha := alpha) (m := m))

/-- Distinct exact first-entry times remain disjoint after pulling the state events back
onto the adaptive pair-path space. -/
theorem pairwise_disjoint_adaptiveCoupledFirstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    Pairwise (Function.onFun Disjoint
      (adaptiveCoupledFirstExactLevelEntrySet V x i)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro path hs ht
  change adaptiveCoupledStatePath path ∈
    transitionTrajectoryFirstExactLevelEntrySet V x i s at hs
  change adaptiveCoupledStatePath path ∈
    transitionTrajectoryFirstExactLevelEntrySet V x i t at ht
  exact
    (Set.disjoint_left.mp
      (pairwise_disjoint_transitionTrajectoryFirstExactLevelEntrySet
        V x i hst)) hs ht

/-- The coupled eventual-entry event is exactly the countable union of its pulled-back
exact-first-entry-time events. -/
theorem iUnion_adaptiveCoupledFirstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    (⋃ T : Nat, adaptiveCoupledFirstExactLevelEntrySet V x i T) =
      adaptiveCoupledEventuallyVisitsExactLevelSet V x i := by
  ext path
  simp [adaptiveCoupledFirstExactLevelEntrySet,
    adaptiveCoupledEventuallyVisitsExactLevelSet,
    transitionTrajectoryEventuallyVisitsExactLevelSet]

/-- Intersecting every exact-time slice with one fixed outer restriction preserves
pairwise disjointness. -/
theorem pairwise_disjoint_restricted_adaptiveCoupledFirstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (A : Set (Nat -> (alpha × (Fin m -> Bool)))) :
    Pairwise (Function.onFun Disjoint
      (fun T => A ∩ adaptiveCoupledFirstExactLevelEntrySet V x i T)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro path hs ht
  exact
    (Set.disjoint_left.mp
      (pairwise_disjoint_adaptiveCoupledFirstExactLevelEntrySet
        V x i hst)) hs.2 ht.2

/-- Under any measurable outer restriction, the genuine coupled eventual-entry mass is
exactly the countable sum of the restricted exact-first-entry-time slice masses. -/
theorem adaptiveCoupled_restricted_eventualEntry_measure_eq_tsum_firstEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (A : Set (Nat -> (alpha × (Fin m -> Bool))))
    (hA : MeasurableSet A) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (A ∩ adaptiveCoupledEventuallyVisitsExactLevelSet V x i) =
      ∑' T : Nat,
        adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (A ∩ adaptiveCoupledFirstExactLevelEntrySet V x i T) := by
  have hset :
      A ∩ adaptiveCoupledEventuallyVisitsExactLevelSet V x i =
        ⋃ T : Nat, A ∩ adaptiveCoupledFirstExactLevelEntrySet V x i T := by
    rw [← iUnion_adaptiveCoupledFirstExactLevelEntrySet V x i]
    ext path
    simp
  rw [hset]
  exact measure_iUnion
    (pairwise_disjoint_restricted_adaptiveCoupledFirstExactLevelEntrySet
      V x i A)
    (fun T => hA.inter
      (measurableSet_adaptiveCoupledFirstExactLevelEntrySet V x i T))

/-- The real restricted-entry mass from fix 55 is the `toReal` of the exact-time
restricted `tsum`.  No interchange of `toReal` and `tsum` is needed here. -/
theorem adaptiveCoupledRestrictedEntryRealMass_eq_toReal_tsum_firstEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (A : Set (Nat -> (alpha × (Fin m -> Bool))))
    (hA : MeasurableSet A) :
    adaptiveCoupledRestrictedEntryRealMass
        P hP V hbound p hp hp1 hexit x i A =
      (∑' T : Nat,
        adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (A ∩ adaptiveCoupledFirstExactLevelEntrySet V x i T)).toReal := by
  unfold adaptiveCoupledRestrictedEntryRealMass
  unfold adaptiveCoupledRestrictedRealMass
  rw [adaptiveCoupled_restricted_eventualEntry_measure_eq_tsum_firstEntry
    P hP V hbound p hp hp1 hexit x i A hA]

/-- At a fixed time `T`, the coupled exact-first-entry event is a finite state cylinder:
it is the inverse image, through the first `T` post-initial state coordinates, of the
finite trajectories whose first exact-level entry occurs at their terminal time. -/
theorem adaptiveCoupledFirstExactLevelEntrySet_eq_statePrefix_preimage
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    adaptiveCoupledFirstExactLevelEntrySet V x i T =
      adaptiveCoupledStatePrefix T ⁻¹'
        {states : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x states i T} := by
  ext path
  change
    transitionTrajectoryFirstVisitsExactLevelAt
        V x i T (adaptiveCoupledStatePath path) ↔
      finiteTrajectoryFirstVisitsExactLevelAt
        V x (adaptiveCoupledStatePrefix T path) i T
  rw [transitionTrajectoryFirstVisitsExactLevelAt_iff_finiteTerminal]
  rfl

/-- The genuine infinite adaptive coupled law assigns each exact first-entry-time event
exactly the already verified terminal coordinate-deleted complement mass.  The proof
uses only the verified finite state marginal of the adaptive coupled law. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_firstExactLevelEntryAt
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m) (T : Nat) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledFirstExactLevelEntrySet V x i T) =
      ENNReal.ofReal
        (terminalFirstEntryComplementMass P V hbound p x i T) := by
  rw [adaptiveCoupledFirstExactLevelEntrySet_eq_statePrefix_preimage V x i T]
  have hprefix : Measurable
      (adaptiveCoupledStatePrefix
        (alpha := alpha) (m := m) T) :=
    measurable_adaptiveCoupledStatePrefix T
  have hset : MeasurableSet
      {states : FiniteTrajectory alpha T |
        finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :=
    ({states : FiniteTrajectory alpha T |
      finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :
      Set (FiniteTrajectory alpha T)).to_countable.measurableSet
  rw [← Measure.map_apply hprefix hset]
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_map_statePrefix_eq_finiteTrajectoryMeasure
    P hP V hbound p hp hp1 hexit x T]
  rw [finiteTrajectoryMeasure_terminalFirstEntrySet P hP V x i T]
  rw [terminalFirstEntryComplementMass_eq_stateSliceMass
    P V hbound p x i T]

/-- As a consistency check, the unrestricted adaptive coupled eventual-entry mass is the
same terminal-complement `tsum` already known for the state-path law. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_eventualExactLevelEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledEventuallyVisitsExactLevelSet V x i) =
      ∑' T : Nat,
        ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T) := by
  calc
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledEventuallyVisitsExactLevelSet V x i) =
      ∑' T : Nat,
        adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (adaptiveCoupledFirstExactLevelEntrySet V x i T) := by
        simpa only [Set.univ_inter] using
          adaptiveCoupled_restricted_eventualEntry_measure_eq_tsum_firstEntry
            P hP V hbound p hp hp1 hexit x i Set.univ MeasurableSet.univ
    _ = ∑' T : Nat,
        ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T) := by
        apply tsum_congr
        intro T
        exact adaptiveMultiLevelCoupledTrajectoryMeasure_firstExactLevelEntryAt
          P hP V hbound p hp hp1 hexit x i T

end ECRuntime
