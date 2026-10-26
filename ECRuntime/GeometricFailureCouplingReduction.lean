import ECRuntime.GeometricCouplingDominationEndpoint
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 52: reduction to a discrete geometric failure-count coupling

Stage 26 fix 51 fix 1 is compiler verified warning-free.  It shows that a joint
measure on adaptive coupled paths and one-based `ENNReal` waiting vectors with the
correct two marginals and almost-everywhere support immediately yields the desired
stochastic-domination endpoint.

The entry/skip calculations developed in fixes 36--46 are naturally stated for the
*number of failures before the first comparison success*, i.e. for values in `Nat`.
This file moves the remaining existence problem back to that discrete space.

We define the finite product of Mathlib's canonical geometric failure-count measures
and prove that componentwise `geometricWaitingTime` pushes this product exactly to the
already verified `geometricWaitingProductMeasure`.  We also record its singleton
masses and a countable-space singleton extensionality interface.  Consequently, the
future construction of the second marginal can be proved by point masses, matching
exactly the form of the existing first-entry/skip branch identities.

Finally, `AdaptiveGeometricFailureCouplingSpec` is the discrete analogue of the fix-51
waiting specification.  A coupling satisfying this failure-count specification already
implies stochastic domination by `geometricWaitingSumMeasure`; no explicit measure map
on the coupling itself is needed.  Thus the remaining hard theorem is reduced to
constructing a coupling whose second coordinate is a finite vector of natural failure
counts with the canonical product-geometric singleton masses.
-/

/-- Finite product law of independent geometric failure counts.  Coordinate `i`
records the number of failures before the first success with parameter `p i`. -/
noncomputable def geometricFailureProductMeasure {m : Nat}
    (p : Fin m -> unitInterval) : Measure (Fin m -> Nat) :=
  Measure.pi (fun i => geometricFailureMeasure (p i))

instance instIsProbabilityMeasureGeometricFailureProductMeasure
    {m : Nat} (p : Fin m -> unitInterval) :
    IsProbabilityMeasure (geometricFailureProductMeasure p) := by
  unfold geometricFailureProductMeasure
  infer_instance

/-- Componentwise conversion of a failure-count vector into the one-based waiting
vector used by `geometricWaitingProductMeasure` is measurable. -/
@[fun_prop] theorem measurable_geometricWaitingVectorOfFailureCounts
    {m : Nat} :
    Measurable
      (geometricWaitingVectorOfFailureCounts :
        (Fin m -> Nat) -> (Fin m -> ENNReal)) := by
  unfold geometricWaitingVectorOfFailureCounts
  fun_prop

/-- Pushing the independent failure-count product law forward coordinatewise by the
one-based waiting map gives exactly the canonical independent waiting-time product law. -/
theorem geometricFailureProductMeasure_map_waitingVector
    {m : Nat} (p : Fin m -> unitInterval) :
    (geometricFailureProductMeasure p).map
        geometricWaitingVectorOfFailureCounts =
      geometricWaitingProductMeasure p := by
  unfold geometricFailureProductMeasure geometricWaitingProductMeasure
  have h := Measure.pi_map_pi
    (μ := fun i : Fin m => geometricFailureMeasure (p i))
    (f := fun _ : Fin m => geometricWaitingTime)
    (fun _ => measurable_geometricWaitingTime.aemeasurable)
  change
    Measure.map (fun failures i => geometricWaitingTime (failures i))
        (Measure.pi (fun i : Fin m => geometricFailureMeasure (p i))) =
      Measure.pi (fun i : Fin m =>
        Measure.map geometricWaitingTime (geometricFailureMeasure (p i)))
  exact h

/-- A singleton of the finite failure-vector product has the expected product of the
coordinate singleton masses.  This is the point-mass interface needed by the upcoming
sequential entry/skip construction. -/
theorem geometricFailureProductMeasure_singleton
    {m : Nat} (p : Fin m -> unitInterval)
    (failures : Fin m -> Nat) :
    geometricFailureProductMeasure p {failures} =
      ∏ i : Fin m, geometricFailureMeasure (p i) {failures i} := by
  classical
  have hset :
      Set.univ.pi (fun i : Fin m => ({failures i} : Set Nat)) =
        ({failures} : Set (Fin m -> Nat)) := by
    ext g
    constructor
    · intro hg
      have hpoint : forall i : Fin m, g i = failures i := by
        intro i
        exact hg i (Set.mem_univ i)
      have hgf : g = failures := funext hpoint
      simp [hgf]
    · intro hg i _hi
      have hgf : g = failures := by simpa using hg
      simp [hgf]
  unfold geometricFailureProductMeasure
  rw [← hset]
  exact Measure.pi_pi (fun i : Fin m => geometricFailureMeasure (p i))
    (fun i : Fin m => ({failures i} : Set Nat))

/-- On the countable failure-vector space, equality of all singleton masses is enough
to identify a candidate second marginal with the canonical geometric product law. -/
theorem measure_eq_geometricFailureProductMeasure_of_singletons
    {m : Nat} (p : Fin m -> unitInterval)
    (nu : Measure (Fin m -> Nat))
    (hsingle : forall failures : Fin m -> Nat,
      nu {failures} = geometricFailureProductMeasure p {failures}) :
    nu = geometricFailureProductMeasure p := by
  exact (Measure.ext_iff_singleton).2 hsingle

/-- Product-form variant of the singleton extensionality theorem. -/
theorem measure_eq_geometricFailureProductMeasure_of_singleton_products
    {m : Nat} (p : Fin m -> unitInterval)
    (nu : Measure (Fin m -> Nat))
    (hsingle : forall failures : Fin m -> Nat,
      nu {failures} =
        ∏ i : Fin m, geometricFailureMeasure (p i) {failures i}) :
    nu = geometricFailureProductMeasure p := by
  apply measure_eq_geometricFailureProductMeasure_of_singletons p nu
  intro failures
  rw [hsingle failures]
  exact (geometricFailureProductMeasure_singleton p failures).symm

/-- Sum of the one-based geometric waiting values associated with a failure-count
vector. -/
noncomputable def geometricFailureVectorWaitingSum
    {m : Nat} (failures : Fin m -> Nat) : ENNReal :=
  geometricWaitingSum (geometricWaitingVectorOfFailureCounts failures)

/-- The failure-vector waiting sum is measurable. -/
@[fun_prop] theorem measurable_geometricFailureVectorWaitingSum
    {m : Nat} :
    Measurable (geometricFailureVectorWaitingSum (m := m)) := by
  unfold geometricFailureVectorWaitingSum
  exact measurable_geometricWaitingSum.comp
    measurable_geometricWaitingVectorOfFailureCounts

/-- The pushed-forward law of the failure-vector waiting sum is exactly the canonical
sum of independent geometric waiting times. -/
theorem geometricFailureProductMeasure_map_waitingSum
    {m : Nat} (p : Fin m -> unitInterval) :
    (geometricFailureProductMeasure p).map
        geometricFailureVectorWaitingSum =
      geometricWaitingSumMeasure p := by
  unfold geometricFailureVectorWaitingSum geometricWaitingSumMeasure
  change
    Measure.map
        (geometricWaitingSum ∘ geometricWaitingVectorOfFailureCounts)
        (geometricFailureProductMeasure p) =
      Measure.map geometricWaitingSum (geometricWaitingProductMeasure p)
  rw [← Measure.map_map
    measurable_geometricWaitingSum
    measurable_geometricWaitingVectorOfFailureCounts]
  rw [geometricFailureProductMeasure_map_waitingVector p]

/-- Runtime tails computed on failure vectors coincide with runtime tails under the
pushed-forward canonical geometric-sum law. -/
theorem geometricFailureVectorWaitingSum_runtimeTailMass
    {m : Nat} (p : Fin m -> unitInterval) (t : ENNReal) :
    runtimeTailMass
        (geometricFailureProductMeasure p)
        geometricFailureVectorWaitingSum t =
      runtimeTailMass (geometricWaitingSumMeasure p) id t := by
  unfold runtimeTailMass runtimeTailEvent
  rw [← geometricFailureProductMeasure_map_waitingSum p]
  change
    geometricFailureProductMeasure p
        (geometricFailureVectorWaitingSum ⁻¹' Set.Ioi t) =
      ((geometricFailureProductMeasure p).map
        geometricFailureVectorWaitingSum) (Set.Ioi t)
  rw [Measure.map_apply
    measurable_geometricFailureVectorWaitingSum measurableSet_Ioi]

/-- Complete support relation on a path/failure-vector pair.  This is the discrete
version of the fix-51 waiting-vector support. -/
def AdaptiveCoupledGeometricFailureCouplingSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (failures : Fin m -> Nat) : Prop :=
  IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path) /\
    HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path) /\
    AdaptiveCoupledGeometricFailureVectorSupport V x path failures

/-- Failure-count support translates pointwise to the waiting-vector support used by
fix 51. -/
theorem adaptiveCoupledGeometricFailureCouplingSupport_to_waitingSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (failures : Fin m -> Nat)
    (hsupport : AdaptiveCoupledGeometricFailureCouplingSupport
      P V hbound p x path failures) :
    AdaptiveCoupledGeometricWaitingCouplingSupport
      P V hbound p x path
        (geometricWaitingVectorOfFailureCounts failures) := by
  rcases hsupport with ⟨hmono, hpositive, hfailures⟩
  refine ⟨hmono, hpositive, ?_⟩
  intro i
  refine ⟨failures i, ?_, hfailures i⟩
  rfl

/-- Every supported path/failure-vector pair satisfies the complete hitting-time bound
against the corresponding geometric waiting sum. -/
theorem adaptiveCoupledPotentialHittingTime_le_geometricFailureVectorWaitingSum_of_support
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (failures : Fin m -> Nat)
    (hsupport : AdaptiveCoupledGeometricFailureCouplingSupport
      P V hbound p x path failures) :
    adaptiveCoupledPotentialHittingTime V x path <=
      geometricFailureVectorWaitingSum failures := by
  unfold geometricFailureVectorWaitingSum
  exact adaptiveCoupledPotentialHittingTime_le_geometricWaitingSum_of_couplingSupport
    P V hbound p x path
      (geometricWaitingVectorOfFailureCounts failures)
      (adaptiveCoupledGeometricFailureCouplingSupport_to_waitingSupport
        P V hbound p x path failures hsupport)

/-- Discrete failure-count formulation of the sole remaining Stage-26 coupling
construction.  Its second marginal lives on a countable space whose singleton masses
are exactly those already exposed by the entry/skip branch calculations. -/
structure AdaptiveGeometricFailureCouplingSpec
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
    ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> Nat))
  firstMarginal : Measure.map
      (Prod.fst :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> Nat)) ->
          (Nat -> (alpha × (Fin m -> Bool)))) couplingMeasure =
    adaptiveMultiLevelCoupledTrajectoryMeasure
      P hP V hbound p hp hp1 hexit x
  secondMarginal : Measure.map
      (Prod.snd :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> Nat)) ->
          (Fin m -> Nat)) couplingMeasure =
    geometricFailureProductMeasure
      (geometricLevelProbabilityVector p hp hp1)
  supported : ∀ᵐ z ∂couplingMeasure,
    AdaptiveCoupledGeometricFailureCouplingSupport
      P V hbound p x z.1 z.2

/-- Constructor variant reducing the discrete second-marginal obligation to singleton
masses.  This is the intended interface for the next sequential branch construction. -/
noncomputable def adaptiveGeometricFailureCouplingSpec_of_secondSingletonProducts
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
      ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> Nat)))
    (hfst : Measure.map
      (Prod.fst :
        ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> Nat)) ->
          (Nat -> (alpha × (Fin m -> Bool)))) kappa =
      adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x)
    (hsingle : forall failures : Fin m -> Nat,
      (Measure.map
        (Prod.snd :
          ((Nat -> (alpha × (Fin m -> Bool))) × (Fin m -> Nat)) ->
            (Fin m -> Nat)) kappa) {failures} =
        ∏ i : Fin m,
          geometricFailureMeasure
            (geometricLevelProbabilityVector p hp hp1 i) {failures i})
    (hsupport : ∀ᵐ z ∂kappa,
      AdaptiveCoupledGeometricFailureCouplingSupport
        P V hbound p x z.1 z.2) :
    AdaptiveGeometricFailureCouplingSpec
      P hP V hbound p hp hp1 hexit x := by
  refine ⟨kappa, hfst, ?_, hsupport⟩
  apply measure_eq_geometricFailureProductMeasure_of_singleton_products
    (geometricLevelProbabilityVector p hp hp1)
  exact hsingle

/-- The discrete failure-count coupling specification already implies the public
stochastic-domination endpoint.  The proof uses the generic product-coupling theorem on
failure vectors and then identifies the comparison tail with the pushed-forward
geometric waiting-sum law. -/
theorem AdaptiveGeometricFailureCouplingSpec.stochasticallyDominated
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (spec : AdaptiveGeometricFailureCouplingSpec
      P hP V hbound p hp hp1 hexit x) :
    StochasticallyDominated
      (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x)
      (adaptiveCoupledPotentialHittingTime V x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector p hp hp1)) id := by
  have hdom :
      StochasticallyDominated
        (adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x)
        (adaptiveCoupledPotentialHittingTime V x)
        (geometricFailureProductMeasure
          (geometricLevelProbabilityVector p hp hp1))
        geometricFailureVectorWaitingSum := by
    apply stochasticallyDominated_of_product_coupling_ae
      (μ := adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x)
      (ν := geometricFailureProductMeasure
        (geometricLevelProbabilityVector p hp hp1))
      (X := adaptiveCoupledPotentialHittingTime V x)
      (Y := geometricFailureVectorWaitingSum)
      (hX := measurable_adaptiveCoupledPotentialHittingTime V x)
      (hY := measurable_geometricFailureVectorWaitingSum)
      (κ := spec.couplingMeasure)
      (hfst := spec.firstMarginal)
      (hsnd := spec.secondMarginal)
    exact spec.supported.mono (fun z hz =>
      adaptiveCoupledPotentialHittingTime_le_geometricFailureVectorWaitingSum_of_support
        P V hbound p x z.1 z.2 hz)
  intro t
  calc
    runtimeTailMass
        (adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x)
        (adaptiveCoupledPotentialHittingTime V x) t <=
      runtimeTailMass
        (geometricFailureProductMeasure
          (geometricLevelProbabilityVector p hp hp1))
        geometricFailureVectorWaitingSum t := hdom t
    _ = runtimeTailMass
        (geometricWaitingSumMeasure
          (geometricLevelProbabilityVector p hp hp1)) id t :=
      geometricFailureVectorWaitingSum_runtimeTailMass
        (geometricLevelProbabilityVector p hp hp1) t

end ECRuntime
