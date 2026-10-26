import ECRuntime.OneLevelGeometricCouplingInterface
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 51: geometric coupling domination endpoint

Stage 26 fix 50 is compiler verified warning-free.  It packages the exact support
relation between a genuine infinite adaptive coupled path and one geometric
failure-count coordinate, lifts that relation to all levels, and identifies the
combined eventual-entry/permanent-skip singleton mass with the canonical geometric
failure-count singleton.

The remaining construction will naturally produce a coupling measure with an
`ENNReal` waiting-time vector as its second component.  This file translates the
failure-count support from fix 50 into that waiting-vector representation and packages
the exact measure-level endpoint consumed by `CouplingDomination.lean`.

The file deliberately does not construct the missing coupling measure.  Instead it
makes its obligations explicit and proves that *any* measure with

* first marginal equal to the genuine infinite adaptive state/vector-label law,
* second marginal equal to the independent geometric waiting product law, and
* almost-everywhere support in the verified adaptive geometric relation

already yields stochastic domination of the zero-potential hitting time by the
canonical sum of independent geometric waiting times.

Thus after this slice the only missing probabilistic theorem is existence of a measure
satisfying this specification.  No further deterministic charge/residence or
coupling-domination bridge is required.
-/

/-- Canonical vector of geometric success parameters associated with the real-valued
level bounds. -/
def geometricLevelProbabilityVector
    {m : Nat} (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1) :
    Fin m -> unitInterval :=
  fun i => probabilityUnitInterval (p i) (le_of_lt (hp i)) (hp1 i)

@[simp] theorem coe_geometricLevelProbabilityVector
    {m : Nat} (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (i : Fin m) :
    ((geometricLevelProbabilityVector p hp hp1 i : unitInterval) : Real) = p i := by
  rfl

/-- Waiting-vector form of the fix-50 all-level support relation.  Every waiting
coordinate must be one plus some natural failure count, and that failure count must be
admissible for the corresponding visited/skip branch. -/
def AdaptiveCoupledGeometricWaitingVectorSupport
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (waiting : Fin m -> ENNReal) : Prop :=
  forall i : Fin m,
    exists r : Nat,
      waiting i = geometricWaitingTime r /\
        AdaptiveCoupledExactLevelGeometricFailureSupport V x path i r

/-- The waiting-vector support relation immediately gives the coordinatewise complete
level-charge bound once potential monotonicity and positive adaptive support are
available. -/
theorem allLevelCharge_le_geometricWaitingVector_of_waitingSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmono : IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path))
    (waiting : Fin m -> ENNReal)
    (hwaiting : AdaptiveCoupledGeometricWaitingVectorSupport V x path waiting) :
    forall i : Fin m,
      trajectoryLevelCharge V x i (adaptiveCoupledStatePath path) <= waiting i := by
  intro i
  rcases hwaiting i with ⟨r, hr, hbranch⟩
  rw [hr]
  exact trajectoryLevelCharge_le_geometricWaitingTime_of_failureSupport
    P V hbound p x (adaptiveCoupledStatePath path) hmono
      (adaptiveCoupledLabelStream path) hsupport i r hbranch

/-- Complete support condition expected from the final joint coupling measure.  The
first two conjuncts are path properties already available almost surely under the
adaptive first marginal (positive support is verified; monotonicity is the intended
fitness-level application premise).  The third conjunct is the waiting-vector support
from this file. -/
def AdaptiveCoupledGeometricWaitingCouplingSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (waiting : Fin m -> ENNReal) : Prop :=
  IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path) /\
    HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path) /\
    AdaptiveCoupledGeometricWaitingVectorSupport V x path waiting

/-- The actual zero-potential hitting time read from the state component of the
infinite adaptive coupled path. -/
noncomputable def adaptiveCoupledPotentialHittingTime
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool))) : ENNReal :=
  transitionTrajectoryFirstHittingTime
    (potentialTarget V) x (adaptiveCoupledStatePath path)

/-- The adaptive coupled zero-potential hitting time is measurable. -/
@[fun_prop] theorem measurable_adaptiveCoupledPotentialHittingTime
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) :
    Measurable (adaptiveCoupledPotentialHittingTime (m := m) V x) := by
  unfold adaptiveCoupledPotentialHittingTime
  exact
    (measurable_transitionTrajectoryFirstHittingTime (potentialTarget V) x).comp
      (measurable_adaptiveCoupledStatePath (alpha := alpha) (m := m))

/-- Any realization in the complete support relation has its actual zero-potential
hitting time bounded by the sum of the supplied waiting vector. -/
theorem adaptiveCoupledPotentialHittingTime_le_geometricWaitingSum_of_couplingSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (waiting : Fin m -> ENNReal)
    (hcoupled : AdaptiveCoupledGeometricWaitingCouplingSupport
      P V hbound p x path waiting) :
    adaptiveCoupledPotentialHittingTime V x path <=
      geometricWaitingSum waiting := by
  rcases hcoupled with ⟨hmono, hpositive, hwaiting⟩
  calc
    adaptiveCoupledPotentialHittingTime V x path <=
        finiteRuntimeSum
          (fun (i : Fin m)
            (path' : Nat -> (alpha × (Fin m -> Bool))) =>
              trajectoryLevelCharge V x i (adaptiveCoupledStatePath path')) path := by
      simpa [adaptiveCoupledPotentialHittingTime, finiteRuntimeSum] using
        (transitionTrajectoryFirstHittingTime_le_levelChargeSum
          V hbound x (adaptiveCoupledStatePath path))
    _ <= geometricWaitingSum waiting := by
      unfold finiteRuntimeSum geometricWaitingSum
      exact Finset.sum_le_sum (fun i _ =>
        allLevelCharge_le_geometricWaitingVector_of_waitingSupport
          P V hbound p x path hmono hpositive waiting hwaiting i)

/-- Raw measure-level endpoint.  Once a joint measure has the correct two marginals and
is almost surely supported on the complete adaptive waiting relation, the actual
zero-potential hitting time is stochastically dominated by the canonical sum law. -/
theorem adaptiveCoupledPotentialHittingTime_stochasticallyDominated_of_waitingCoupling
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (kappa : Measure
      ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> ENNReal)))
    (hfst : Measure.map
      (Prod.fst :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> ENNReal)) ->
          (Nat -> (alpha × (Fin m -> Bool)))) kappa =
      adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x)
    (hsnd : Measure.map
      (Prod.snd :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> ENNReal)) ->
          (Fin m -> ENNReal)) kappa =
      geometricWaitingProductMeasure
        (geometricLevelProbabilityVector p hp hp1))
    (hsupport : ∀ᵐ z ∂kappa,
      AdaptiveCoupledGeometricWaitingCouplingSupport
        P V hbound p x z.1 z.2) :
    StochasticallyDominated
      (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x)
      (adaptiveCoupledPotentialHittingTime V x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector p hp hp1)) id := by
  apply stochasticallyDominated_by_geometricWaitingSumMeasure_of_coupling_ae
    (μ := adaptiveMultiLevelCoupledTrajectoryMeasure
      P hP V hbound p hp hp1 hexit x)
    (X := adaptiveCoupledPotentialHittingTime V x)
    (hX := measurable_adaptiveCoupledPotentialHittingTime V x)
    (p := geometricLevelProbabilityVector p hp hp1)
    (κ := kappa)
    (hfst := hfst) (hsnd := hsnd)
  exact hsupport.mono (fun z hz =>
    adaptiveCoupledPotentialHittingTime_le_geometricWaitingSum_of_couplingSupport
      P V hbound p x z.1 z.2 hz)

/-- Bundled specification for the one remaining Stage-26 probabilistic construction. -/
structure AdaptiveGeometricWaitingCouplingSpec
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) where
  couplingMeasure : Measure
    ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> ENNReal))
  firstMarginal : Measure.map
      (Prod.fst :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> ENNReal)) ->
          (Nat -> (alpha × (Fin m -> Bool)))) couplingMeasure =
    adaptiveMultiLevelCoupledTrajectoryMeasure
      P hP V hbound p hp hp1 hexit x
  secondMarginal : Measure.map
      (Prod.snd :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> ENNReal)) ->
          (Fin m -> ENNReal)) couplingMeasure =
    geometricWaitingProductMeasure
      (geometricLevelProbabilityVector p hp hp1)
  supported : ∀ᵐ z ∂couplingMeasure,
    AdaptiveCoupledGeometricWaitingCouplingSupport
      P V hbound p x z.1 z.2

/-- Bundled endpoint: constructing `AdaptiveGeometricWaitingCouplingSpec` is sufficient
for the desired stochastic domination on the genuine adaptive coupled process. -/
theorem AdaptiveGeometricWaitingCouplingSpec.stochasticallyDominated
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (spec : AdaptiveGeometricWaitingCouplingSpec
      P hP V hbound p hp hp1 hexit x) :
    StochasticallyDominated
      (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x)
      (adaptiveCoupledPotentialHittingTime V x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector p hp hp1)) id := by
  exact adaptiveCoupledPotentialHittingTime_stochasticallyDominated_of_waitingCoupling
    P hP V hbound p hp hp1 hexit x
      spec.couplingMeasure spec.firstMarginal spec.secondMarginal spec.supported

end ECRuntime
