import ECRuntime.LevelChargeWaitingBridge
import ECRuntime.ExactLevelGeometricBranchAssembly
import ECRuntime.CouplingDomination
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 50: one-level geometric coupling support interface

Stage 26 fix 49 fix 1 is compiler verified warning-free.  The complete exact-level
charge used by `CouplingDomination.lean` is therefore bounded by the history-dependent
first-comparison-success waiting time on a visited level, while a permanently skipped
level has zero charge.

The remaining probabilistic construction must put the genuine adaptive trajectory and a
geometric comparison coordinate on one common space.  Before constructing that measure,
this file packages the exact support and marginal contract it must satisfy.

For a failure count `r`, a path/label realization is in the one-level support when either

* the exact level is visited, a post-entry comparison success exists, and its verified
  first-success offset is exactly `r`; or
* the exact level is permanently skipped.

On both branches the complete `trajectoryLevelCharge` is bounded by the canonical
one-based waiting value `geometricWaitingTime r`.  The interface is then lifted to all
levels and finite sums.  Separately, the Stage-26 fix-46 branch masses are repackaged as
one scalar and identified exactly with the singleton mass of Mathlib's canonical
geometric failure-count law.

No joint measure is claimed here.  The next slice only has to construct a measure
concentrated on these support slices and prove that its failure-count vector has the
independent geometric product law; the already verified coupling-domination theorem can
then be invoked without another deterministic bridge.
-/

/-- One-level support relation between an adaptive path/label realization and a
geometric failure count.  The first branch records the actual post-entry first-success
offset; the second branch records permanent skipping. -/
def ExactLevelGeometricFailureSupport
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m) (r : Nat) : Prop :=
  (∃ hvisit : (∃ t : Nat,
      V (transitionTrajectoryState x path t) = i.val + 1),
    ∃ hsucc : (∃ k : Nat,
      labels (firstExactLevelEntryTime V x path i hvisit + k) i = true),
      firstComparisonSuccessOffsetAfterEntry
        V x path labels i hvisit hsucc = r) ∨
  (∀ t : Nat,
    V (transitionTrajectoryState x path t) ≠ i.val + 1)

/-- A realized visited-level first-success offset belongs to the corresponding support
slice. -/
theorem exactLevelGeometricFailureSupport_of_visit_success
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : ∃ t : Nat,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ k : Nat,
      labels (firstExactLevelEntryTime V x path i hvisit + k) i = true) :
    ExactLevelGeometricFailureSupport V x path labels i
      (firstComparisonSuccessOffsetAfterEntry
        V x path labels i hvisit hsucc) := by
  left
  exact ⟨hvisit, hsucc, rfl⟩

/-- A permanently skipped level belongs to every failure-count support slice.  This is
intentional: its actual charge is zero, so any fresh geometric comparison value is
admissible on the skip branch. -/
theorem exactLevelGeometricFailureSupport_of_skip
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hskip : ∀ t : Nat,
      V (transitionTrajectoryState x path t) ≠ i.val + 1)
    (r : Nat) :
    ExactLevelGeometricFailureSupport V x path labels i r := by
  right
  exact hskip

/-- Main one-level support theorem: every admissible failure-count branch bounds the
complete exact-level charge by the canonical one-based geometric waiting value. -/
theorem trajectoryLevelCharge_le_geometricWaitingTime_of_failureSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : Nat -> (Fin m -> Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x path labels)
    (i : Fin m) (r : Nat)
    (hbranch : ExactLevelGeometricFailureSupport
      V x path labels i r) :
    trajectoryLevelCharge V x i path <= geometricWaitingTime r := by
  rcases hbranch with hentry | hskip
  · rcases hentry with ⟨hvisit, hsucc, hr⟩
    exact trajectoryLevelCharge_le_geometricWaitingTime_of_firstComparisonSuccessOffset
      P V hbound p x path hmono labels hsupport i hvisit hsucc r hr
  · exact trajectoryLevelCharge_le_geometricWaitingTime_of_never_visits_exactLevel
      V x path i hskip r

/-- Support relation specialized to one sample of the genuine infinite adaptive coupled
pair process. -/
def AdaptiveCoupledExactLevelGeometricFailureSupport
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (i : Fin m) (r : Nat) : Prop :=
  ExactLevelGeometricFailureSupport
    V x (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path) i r

/-- Almost-everywhere one-level support implication on the genuine infinite adaptive
coupled law.  Fix 48 fix 2 supplies positive adaptive support; monotonicity remains the
separate application premise. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_ae_charge_le_waiting_of_failureSupport
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (hmono : ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path)) :
    ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      forall (i : Fin m) (r : Nat),
        AdaptiveCoupledExactLevelGeometricFailureSupport V x path i r ->
          trajectoryLevelCharge V x i (adaptiveCoupledStatePath path) <=
            geometricWaitingTime r := by
  filter_upwards
    [hmono,
      adaptiveMultiLevelCoupledTrajectoryMeasure_ae_positiveAdaptiveSupport
        P hP V hbound p hp hp1 hexit x] with path hmonoPath hsupport
  intro i r hbranch
  exact trajectoryLevelCharge_le_geometricWaitingTime_of_failureSupport
    P V hbound p x (adaptiveCoupledStatePath path) hmonoPath
      (adaptiveCoupledLabelStream path) hsupport i r hbranch

/-- Coordinatewise support relation for a complete vector of geometric failure counts. -/
def AdaptiveCoupledGeometricFailureVectorSupport
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (failures : Fin m -> Nat) : Prop :=
  forall i : Fin m,
    AdaptiveCoupledExactLevelGeometricFailureSupport
      V x path i (failures i)

/-- Convert a vector of failure counts into the one-based `ENNReal` waiting vector used
by the geometric product law. -/
def geometricWaitingVectorOfFailureCounts
    {m : Nat} (failures : Fin m -> Nat) : Fin m -> ENNReal :=
  fun i => geometricWaitingTime (failures i)

@[simp] theorem geometricWaitingVectorOfFailureCounts_apply
    {m : Nat} (failures : Fin m -> Nat) (i : Fin m) :
    geometricWaitingVectorOfFailureCounts failures i =
      geometricWaitingTime (failures i) := by
  rfl

/-- Coordinatewise all-level version of the deterministic support theorem. -/
theorem allLevelCharge_le_geometricWaitingVector_of_failureSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmono : IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path))
    (failures : Fin m -> Nat)
    (hbranch : AdaptiveCoupledGeometricFailureVectorSupport
      V x path failures) :
    forall i : Fin m,
      trajectoryLevelCharge V x i (adaptiveCoupledStatePath path) <=
        geometricWaitingVectorOfFailureCounts failures i := by
  intro i
  exact trajectoryLevelCharge_le_geometricWaitingTime_of_failureSupport
    P V hbound p x (adaptiveCoupledStatePath path) hmono
      (adaptiveCoupledLabelStream path) hsupport i (failures i) (hbranch i)

/-- Summing the all-level support bounds gives exactly the geometric waiting sum of the
failure-count vector. -/
theorem sum_levelCharges_le_geometricWaitingSum_of_failureSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmono : IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path))
    (failures : Fin m -> Nat)
    (hbranch : AdaptiveCoupledGeometricFailureVectorSupport
      V x path failures) :
    (∑ i : Fin m,
      trajectoryLevelCharge V x i (adaptiveCoupledStatePath path)) <=
      geometricWaitingSum (geometricWaitingVectorOfFailureCounts failures) := by
  unfold geometricWaitingSum
  exact Finset.sum_le_sum (fun i _ =>
    allLevelCharge_le_geometricWaitingVector_of_failureSupport
      P V hbound p x path hmono hsupport failures hbranch i)

/-- Scalar mass of one geometric failure-count branch after combining eventual entry
and permanent skipping. -/
noncomputable def exactLevelGeometricFailureBranchMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (r : Nat) : ENNReal :=
  eventualExactLevelEntryGeometricFailureMass
      P hP V p x i hp0 hp1 r +
    permanentSkipExactLevelGeometricFailureMass
      P hP V p x i hp0 hp1 r

/-- The combined support-branch mass is exactly the singleton mass of the canonical
geometric failure-count measure. -/
theorem exactLevelGeometricFailureBranchMass_eq_geometricFailureMeasure_singleton
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (r : Nat) :
    exactLevelGeometricFailureBranchMass
        P hP V p x i hp0 hp1 r =
      geometricFailureMeasure
        (probabilityUnitInterval (p i) hp0 hp1) {r} := by
  unfold exactLevelGeometricFailureBranchMass
  exact eventualEntry_add_permanentSkip_geometricFailureMass
    P hP V p x i hp0 hp1 r

/-- Explicit geometric singleton form for a strictly positive level parameter. -/
theorem exactLevelGeometricFailureBranchMass_eq_pattern
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp : 0 < p i) (hp1 : p i <= 1)
    (r : Nat) :
    exactLevelGeometricFailureBranchMass
        P hP V p x i (le_of_lt hp) hp1 r =
      ENNReal.ofReal ((1 - p i) ^ r * p i) := by
  unfold exactLevelGeometricFailureBranchMass
  exact eventualEntry_add_permanentSkip_geometricFailureMass_eq_pattern
    P hP V p x i hp hp1 r

end ECRuntime
