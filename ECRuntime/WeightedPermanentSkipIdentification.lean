import ECRuntime.WeightedEntrySkipGeometricPeeling
import ECRuntime.InfiniteAdaptiveCoupledTrajectory
import ECRuntime.EventualExactLevelEntry
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 55: restricted permanent-skip mass identification

Stage 26 fix 54 is compiler verified warning-free.  It proves the one-coordinate
entry/skip geometric peeling identity with an abstract real scalar `skipMass` standing
for the portion of an already-restricted branch that permanently skips exact level
`i+1`.

This file identifies that scalar with an actual event under the genuine infinite
adaptive coupled trajectory law.  Let `A` be any measurable restriction of the coupled
path space; later `A` will encode failure counts already fixed for previously peeled
coordinates.  Pull the exact-level eventual-entry event back through the state-path
projection of the coupled process and intersect it with `A`.  The complementary
intersection is the genuine restricted permanent-skip branch.

Because eventual entry and permanent skip are complements, these two restricted events
are disjoint and their masses add exactly to the mass of `A`.  The coupled law is a
probability measure, so all three masses are finite and the same partition identity can
be transported through `ENNReal.toReal`.  Consequently the abstract `skipMass` in fix
54 can be instantiated by the real mass of the genuine restricted skip event.

The final theorem combines this identification with the verified fix-54 peeling
identity.  Its only remaining hypothesis is the visited-branch bridge: the weighted
first-entry complement mass from fix 53 must be identified with the real mass of
`A` intersected with eventual entry.  Establishing that bridge for restrictions that
encode an already-fixed failure-vector prefix is the next substantive step toward the
complete-vector product formula.
-/

/-- Eventual visit of exact level `i+1`, viewed on the genuine adaptive coupled path
space through its state projection. -/
def adaptiveCoupledEventuallyVisitsExactLevelSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  adaptiveCoupledStatePath ⁻¹'
    transitionTrajectoryEventuallyVisitsExactLevelSet V x i

/-- Permanent skip of exact level `i+1` on the genuine adaptive coupled path space. -/
def adaptiveCoupledPermanentlySkipsExactLevelSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  (adaptiveCoupledEventuallyVisitsExactLevelSet V x i)ᶜ

/-- The coupled eventual-entry event is measurable. -/
theorem measurableSet_adaptiveCoupledEventuallyVisitsExactLevelSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    MeasurableSet (adaptiveCoupledEventuallyVisitsExactLevelSet V x i) := by
  unfold adaptiveCoupledEventuallyVisitsExactLevelSet
  exact
    (measurableSet_transitionTrajectoryEventuallyVisitsExactLevelSet V x i).preimage
      (measurable_adaptiveCoupledStatePath (alpha := alpha) (m := m))

/-- The coupled permanent-skip event is measurable. -/
theorem measurableSet_adaptiveCoupledPermanentlySkipsExactLevelSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    MeasurableSet (adaptiveCoupledPermanentlySkipsExactLevelSet V x i) := by
  unfold adaptiveCoupledPermanentlySkipsExactLevelSet
  exact (measurableSet_adaptiveCoupledEventuallyVisitsExactLevelSet V x i).compl

/-- Under any measurable outer restriction `A`, eventual entry and permanent skipping
remain a disjoint partition of `A`.  This is the exact event-level form needed when
`A` records failure counts already peeled from other coordinates. -/
theorem restricted_adaptiveCoupled_entry_add_skip_measure
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
        (A ∩ adaptiveCoupledEventuallyVisitsExactLevelSet V x i) +
      adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (A ∩ adaptiveCoupledPermanentlySkipsExactLevelSet V x i) =
      adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x A := by
  let E : Set (Nat -> (alpha × (Fin m -> Bool))) :=
    adaptiveCoupledEventuallyVisitsExactLevelSet V x i
  let S : Set (Nat -> (alpha × (Fin m -> Bool))) :=
    adaptiveCoupledPermanentlySkipsExactLevelSet V x i
  have hS : S = Eᶜ := by
    rfl
  have hSmeas : MeasurableSet S := by
    exact measurableSet_adaptiveCoupledPermanentlySkipsExactLevelSet V x i
  have hdisj : Disjoint (A ∩ E) (A ∩ S) := by
    apply Set.disjoint_left.mpr
    intro z hzEntry hzSkip
    have hzE : z ∈ E := hzEntry.2
    rw [hS] at hzSkip
    exact hzSkip.2 hzE
  have hunion : (A ∩ E) ∪ (A ∩ S) = A := by
    rw [hS]
    ext z
    by_cases hz : z ∈ E <;> simp
  calc
    adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x (A ∩ E) +
        adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x (A ∩ S) =
      adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x ((A ∩ E) ∪ (A ∩ S)) := by
        symm
        exact measure_union hdisj (hA.inter hSmeas)
    _ = adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x A := by
        rw [hunion]

/-- Real mass of an arbitrary measurable restriction under the genuine infinite
adaptive coupled law.  The probability-law assumption ensures this is a lossless
finite-mass representation. -/
noncomputable def adaptiveCoupledRestrictedRealMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (A : Set (Nat -> (alpha × (Fin m -> Bool)))) : Real :=
  (adaptiveMultiLevelCoupledTrajectoryMeasure
    P hP V hbound p hp hp1 hexit x A).toReal

/-- Real mass of the restricted eventual-entry branch. -/
noncomputable def adaptiveCoupledRestrictedEntryRealMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (A : Set (Nat -> (alpha × (Fin m -> Bool)))) : Real :=
  adaptiveCoupledRestrictedRealMass P hP V hbound p hp hp1 hexit x
    (A ∩ adaptiveCoupledEventuallyVisitsExactLevelSet V x i)

/-- Real mass of the genuine restricted permanent-skip branch.  This is the concrete
`skipMass` that replaces the abstract scalar from fix 54. -/
noncomputable def adaptiveCoupledRestrictedPermanentSkipRealMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (A : Set (Nat -> (alpha × (Fin m -> Bool)))) : Real :=
  adaptiveCoupledRestrictedRealMass P hP V hbound p hp hp1 hexit x
    (A ∩ adaptiveCoupledPermanentlySkipsExactLevelSet V x i)

/-- The restricted entry and genuine restricted permanent-skip real masses add exactly
to the real mass of the previous-coordinate restriction. -/
theorem adaptiveCoupledRestrictedEntryRealMass_add_permanentSkipRealMass
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
        P hP V hbound p hp hp1 hexit x i A +
      adaptiveCoupledRestrictedPermanentSkipRealMass
        P hP V hbound p hp hp1 hexit x i A =
      adaptiveCoupledRestrictedRealMass
        P hP V hbound p hp hp1 hexit x A := by
  unfold adaptiveCoupledRestrictedEntryRealMass
  unfold adaptiveCoupledRestrictedPermanentSkipRealMass
  unfold adaptiveCoupledRestrictedRealMass
  have hentryTop :
      adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (A ∩ adaptiveCoupledEventuallyVisitsExactLevelSet V x i) ≠ ∞ := by
    exact measure_ne_top _ _
  have hskipTop :
      adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (A ∩ adaptiveCoupledPermanentlySkipsExactLevelSet V x i) ≠ ∞ := by
    exact measure_ne_top _ _
  rw [← ENNReal.toReal_add hentryTop hskipTop]
  exact congrArg ENNReal.toReal
    (restricted_adaptiveCoupled_entry_add_skip_measure
      P hP V hbound p hp hp1 hexit x i A hA)

/-- Concrete replacement of the abstract fix-54 skip scalar.

Once the weighted visited-branch complement mass has been identified with the genuine
restricted eventual-entry mass, adding the genuine restricted permanent-skip mass gives
exactly the total restricted mass. -/
theorem weightedEntrySkipComplementMass_eq_adaptiveCoupledRestrictedRealMass
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (paths : beta -> Nat -> alpha)
    (labels : beta -> Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : forall a : beta, Exists fun s =>
      V (transitionTrajectoryState x (paths a) s) = i.val + 1)
    (w : beta -> Real)
    (A : Set (Nat -> (alpha × (Fin m -> Bool))))
    (hA : MeasurableSet A)
    (hentry : weightedFirstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit w =
        adaptiveCoupledRestrictedEntryRealMass
          P hP V hbound p hp hp1 hexit x i A) :
    weightedEntrySkipComplementMass
        P V hbound p x paths labels i hvisit w
          (adaptiveCoupledRestrictedPermanentSkipRealMass
            P hP V hbound p hp hp1 hexit x i A) =
      adaptiveCoupledRestrictedRealMass
        P hP V hbound p hp hp1 hexit x A := by
  unfold weightedEntrySkipComplementMass
  rw [hentry]
  exact adaptiveCoupledRestrictedEntryRealMass_add_permanentSkipRealMass
    P hP V hbound p hp hp1 hexit x i A hA

/-- Restricted one-coordinate peeling with the permanent-skip branch fully concrete.
The only remaining bridge is `hentry`, identifying the weighted visited histories with
the genuine restricted eventual-entry mass. -/
theorem weightedEntrySkipGeometricFailurePatternMass_eq_restrictedRealMass_mul_pattern
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (paths : beta -> Nat -> alpha)
    (labels : beta -> Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : forall a : beta, Exists fun s =>
      V (transitionTrajectoryState x (paths a) s) = i.val + 1)
    (w : beta -> Real)
    (A : Set (Nat -> (alpha × (Fin m -> Bool))))
    (hA : MeasurableSet A)
    (hentry : weightedFirstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit w =
        adaptiveCoupledRestrictedEntryRealMass
          P hP V hbound p hp hp1 hexit x i A)
    (r : Nat) :
    weightedEntrySkipGeometricFailurePatternMass
        P V hbound p x paths labels i hvisit w
          (adaptiveCoupledRestrictedPermanentSkipRealMass
            P hP V hbound p hp hp1 hexit x i A) r =
      adaptiveCoupledRestrictedRealMass
          P hP V hbound p hp hp1 hexit x A *
        ((1 - p i) ^ r * p i) := by
  exact weightedEntrySkipGeometricFailurePatternMass_eq_of_mass
    P V hbound p x paths labels i hvisit w
      (adaptiveCoupledRestrictedPermanentSkipRealMass
        P hP V hbound p hp hp1 hexit x i A)
      (adaptiveCoupledRestrictedRealMass
        P hP V hbound p hp hp1 hexit x A)
      r
      (weightedEntrySkipComplementMass_eq_adaptiveCoupledRestrictedRealMass
        P hP V hbound p hp hp1 hexit x paths labels i hvisit w A hA hentry)

end ECRuntime
