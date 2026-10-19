import ECRuntime.RestrictedFirstEntryTimeDecomposition
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 57: finite-cylinder localization of restricted first entry

Stage 26 fix 56 is compiler verified warning-free.  It decomposes a genuinely
restricted eventual-entry event into the countable disjoint sum of its exact first-entry
time slices.  The next task is therefore local in one fixed time `T`.

For the sequential failure-vector proof the restrictions already imposed before peeling
coordinate `i` are chosen from higher potential levels.  If exact level `i+1` is first
entered at time `T`, all information from those higher levels lies in the first `T`
post-initial coupled transitions.  Hence the relevant restriction at this slice is a
finite cylinder.

This file makes that localization explicit.  An arbitrary set `B` of finite coupled
pair prefixes is pulled back through `transitionTrajectoryTail T`.  The verified
infinite-to-finite marginal theorem from fix 47 identifies the mass of that cylinder
exactly with the finite adaptive coupled measure.  Intersecting with first entry at time
`T` becomes intersection with a finite terminal-first-entry set.

The final definitions erase the currently peeled comparison coordinate `i` from the
finite prefix.  Any restriction pulled back through this deleted-coordinate projection
is automatically insensitive to the pre-entry values of coordinate `i`, exactly the
invariance needed by the pre-entry marginalization machinery from fixes 32--43.

The next stage can therefore stay entirely finite: evaluate the finite coupled measure
of a deleted-coordinate restriction intersected with the terminal first-entry set as a
coordinate-deleted weighted history sum.  That is the missing local mass identity to be
summed by fix 56.
-/

/-- A finite pair-prefix event, pulled back to the genuine infinite adaptive coupled
path space through the first `T` post-initial coordinates. -/
def adaptiveCoupledPairPrefixCylinderSet
    {alpha : Type*} {m T : Nat}
    (B : Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T)) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  transitionTrajectoryTail T ⁻¹' B

/-- Every finite pair-prefix cylinder is measurable. -/
theorem measurableSet_adaptiveCoupledPairPrefixCylinderSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (B : Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T)) :
    MeasurableSet (adaptiveCoupledPairPrefixCylinderSet B) := by
  unfold adaptiveCoupledPairPrefixCylinderSet
  exact B.to_countable.measurableSet.preimage
    (measurable_transitionTrajectoryTail
      (α := alpha × (Fin m -> Bool)) T)

/-- Finite pair prefixes whose state component first visits exact positive level `i+1`
precisely at the terminal time `T`. -/
def finiteCoupledTerminalFirstEntrySet
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T) :=
  {path | finiteTrajectoryFirstVisitsExactLevelAt
    V x (finiteCoupledStateProjection path) i T}

/-- The exact first-entry event from fix 56 is itself the pair-prefix cylinder of the
finite terminal-first-entry set. -/
theorem adaptiveCoupledFirstExactLevelEntrySet_eq_pairPrefixCylinder
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    adaptiveCoupledFirstExactLevelEntrySet V x i T =
      adaptiveCoupledPairPrefixCylinderSet (T := T)
        (finiteCoupledTerminalFirstEntrySet (T := T) V x i) := by
  rw [adaptiveCoupledFirstExactLevelEntrySet_eq_statePrefix_preimage V x i T]
  rfl

/-- The mass of any finite pair-prefix cylinder under the genuine infinite adaptive
coupled law is exactly its mass under the verified finite coupled measure. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_pairPrefixCylinder
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (B : Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T)) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledPairPrefixCylinderSet B) =
      finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit T x B := by
  have htail : Measurable
      (transitionTrajectoryTail
        (α := alpha × (Fin m -> Bool)) T) :=
    measurable_transitionTrajectoryTail
      (α := alpha × (Fin m -> Bool)) T
  have hB : MeasurableSet B := B.to_countable.measurableSet
  unfold adaptiveCoupledPairPrefixCylinderSet
  rw [← Measure.map_apply htail hB]
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_map_tail_eq_finiteCoupledMeasure
    P hP V hbound p hp hp1 hexit x T]

/-- Intersecting a finite prefix restriction with exact first entry at time `T` stays
inside the same finite prefix: it is the cylinder of the corresponding finite
intersection. -/
theorem adaptiveCoupledPairPrefixCylinder_inter_firstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat)
    (B : Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T)) :
    adaptiveCoupledPairPrefixCylinderSet B ∩
        adaptiveCoupledFirstExactLevelEntrySet V x i T =
      adaptiveCoupledPairPrefixCylinderSet
        (B ∩ finiteCoupledTerminalFirstEntrySet (T := T) V x i) := by
  rw [adaptiveCoupledFirstExactLevelEntrySet_eq_pairPrefixCylinder V x i T]
  ext path
  rfl

/-- Exact finite localization of a restricted first-entry-time slice.  No infinite
history remains on the right-hand side. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_pairPrefix_restricted_firstEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m) (T : Nat)
    (B : Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T)) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledPairPrefixCylinderSet B ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T) =
      finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit T x
        (B ∩ finiteCoupledTerminalFirstEntrySet (T := T) V x i) := by
  rw [adaptiveCoupledPairPrefixCylinder_inter_firstExactLevelEntrySet
    V x i T B]
  exact adaptiveMultiLevelCoupledTrajectoryMeasure_pairPrefixCylinder
    P hP V hbound p hp hp1 hexit x
      (B ∩ finiteCoupledTerminalFirstEntrySet (T := T) V x i)

/-- Delete coordinate `i` from every emitted label in a finite coupled pair prefix while
retaining the state component. -/
def finiteCoupledDeletedCoordinateProjection
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) T) :
    FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T :=
  fun t => ((path t).1, inactiveCoordinateRepresentative i (path t).2)

/-- Deleting coordinate `i` is unchanged if that coordinate is overwritten first. -/
theorem inactiveCoordinateRepresentative_update_self
    {m : Nat} (i : Fin m) (bits : Fin m -> Bool) (b : Bool) :
    inactiveCoordinateRepresentative i (Function.update bits i b) =
      inactiveCoordinateRepresentative i bits := by
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp [inactiveCoordinateRepresentative]
  · simp [inactiveCoordinateRepresentative, hji]

/-- A restriction on finite state/deleted-label prefixes, pulled back to full finite
coupled prefixes.  By construction it cannot inspect coordinate `i`. -/
def finiteCoupledDeletedCoordinateRestrictionSet
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T) :=
  finiteCoupledDeletedCoordinateProjection i ⁻¹' C

/-- Overwriting the peeled coordinate throughout a finite full-label trajectory does
not change its deleted-coordinate projection. -/
theorem finiteCoupledDeletedCoordinateProjection_updateLabelTrajectory
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (states : FiniteTrajectory alpha T)
    (labels : FiniteTrajectory (Fin m -> Bool) T)
    (coord : FiniteTrajectory Bool T) :
    finiteCoupledDeletedCoordinateProjection i
        (zipFiniteTrajectories states
          (fun t => Function.update (labels t) i (coord t))) =
      finiteCoupledDeletedCoordinateProjection i
        (zipFiniteTrajectories states labels) := by
  funext t
  apply Prod.ext
  · rfl
  · exact inactiveCoordinateRepresentative_update_self
      i (labels t) (coord t)

/-- Infinite-path version of a finite restriction that observes the state and all label
coordinates except the coordinate currently being peeled. -/
def adaptiveCoupledDeletedCoordinatePrefixRestrictionSet
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  adaptiveCoupledPairPrefixCylinderSet
    (finiteCoupledDeletedCoordinateRestrictionSet i C)

/-- Deleted-coordinate finite-prefix restrictions are measurable on the genuine
infinite adaptive coupled path space. -/
theorem measurableSet_adaptiveCoupledDeletedCoordinatePrefixRestrictionSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    MeasurableSet (adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i C) := by
  unfold adaptiveCoupledDeletedCoordinatePrefixRestrictionSet
  exact measurableSet_adaptiveCoupledPairPrefixCylinderSet
    (finiteCoupledDeletedCoordinateRestrictionSet i C)

/-- The restricted exact-time mass for a deleted-coordinate prefix condition is exactly
a finite coupled measure of the corresponding deleted-coordinate restriction and
terminal first-entry event.  This is the finite measure target for the next weighted
history calculation. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m) (T : Nat)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i C ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T) =
      finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit T x
        (finiteCoupledDeletedCoordinateRestrictionSet i C ∩
          finiteCoupledTerminalFirstEntrySet (T := T) V x i) := by
  unfold adaptiveCoupledDeletedCoordinatePrefixRestrictionSet
  exact adaptiveMultiLevelCoupledTrajectoryMeasure_pairPrefix_restricted_firstEntry
    P hP V hbound p hp hp1 hexit x i T
      (finiteCoupledDeletedCoordinateRestrictionSet i C)

end ECRuntime
