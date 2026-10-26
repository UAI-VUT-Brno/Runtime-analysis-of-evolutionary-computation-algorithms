import ECRuntime.DirectGeometricTailDominationClosed
import ECRuntime.NatTailToStochasticDomination
import Mathlib

namespace ECRuntime

/-!
# Stage 26 fix 71: closed full stochastic-domination endpoint

Stage 26 fix 70 closes the direct Bellman comparison at every natural threshold.
The generic integer/`⊤` bridge from `NatTailToStochasticDomination.lean` upgrades that
result to all `ENNReal` thresholds.  To keep the comparison observable pointwise
integer-valued, the bridge is applied first on the geometric failure-count product;
the already verified push-forward identity then transports the result to the public
`geometricWaitingSumMeasure` law.
-/

/-- Full first-order stochastic domination for a bounded nonincreasing potential with
uniform exact-level exit probabilities.  This is the closed distributional fitness-
level endpoint of Stage 26. -/
theorem stochasticallyDominated_transitionTrajectoryPotentialHittingTime_geometricWaitingSum
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : alpha) :
    StochasticallyDominated
      (transitionTrajectoryMeasure P hP x)
      (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector p hp hp1)) id := by
  classical
  let q : Fin m -> unitInterval := geometricLevelProbabilityVector p hp hp1
  have hNatSum :
      NatTailDominated
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
        (geometricWaitingSumMeasure q) id := by
    simpa [q] using
      natTailDominated_transitionTrajectoryPotentialHittingTime_geometricWaitingSum
        P hP V hbound p hp hp1 hexit hmonoP x
  have hNatFailure :
      NatTailDominated
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
        (geometricFailureProductMeasure q)
        geometricFailureVectorWaitingSum := by
    intro k
    calc
      runtimeTailMass
          (transitionTrajectoryMeasure P hP x)
          (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
          (k : ENNReal) <=
        runtimeTailMass (geometricWaitingSumMeasure q) id (k : ENNReal) :=
          hNatSum k
      _ = runtimeTailMass
          (geometricFailureProductMeasure q)
          geometricFailureVectorWaitingSum (k : ENNReal) := by
        symm
        exact geometricFailureVectorWaitingSum_runtimeTailMass q (k : ENNReal)
  have hFullFailure :
      StochasticallyDominated
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
        (geometricFailureProductMeasure q)
        geometricFailureVectorWaitingSum :=
    stochasticallyDominated_of_natTailDominated_of_natOrTopValued
      (isNatOrTopValued_transitionTrajectoryFirstHittingTime
        (potentialTarget V) x)
      isNatOrTopValued_geometricFailureVectorWaitingSum
      hNatFailure
  intro t
  calc
    runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x) t <=
      runtimeTailMass
        (geometricFailureProductMeasure q)
        geometricFailureVectorWaitingSum t := hFullFailure t
    _ = runtimeTailMass (geometricWaitingSumMeasure q) id t :=
      geometricFailureVectorWaitingSum_runtimeTailMass q t

end ECRuntime
