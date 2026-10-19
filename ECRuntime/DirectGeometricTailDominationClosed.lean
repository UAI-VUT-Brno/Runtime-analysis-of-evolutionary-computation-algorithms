import ECRuntime.GeometricSumTailIdentification
import Mathlib

namespace ECRuntime

/-!
# Stage 26 fix 70: closed natural-threshold domination endpoint

The geometric-sum tail identification discharges the sole abstract assumption
left by Stage 26 fix 69.  The process-side Bellman argument therefore yields a
closed natural-threshold domination theorem with no coupling-construction
hypothesis.
-/

/-- Closed direct natural-threshold domination theorem for a bounded
nonincreasing potential with uniform exact-level exit probabilities. -/
theorem natTailDominated_transitionTrajectoryPotentialHittingTime_geometricWaitingSum
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
    NatTailDominated
      (transitionTrajectoryMeasure P hP x)
      (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector p hp hp1)) id := by
  exact
    natTailDominated_transitionTrajectoryPotentialHittingTime_geometricWaitingSum_of_identification
      P hP V hbound p hp hp1 hexit hmonoP x
      (hasGeometricSumTailIdentification_geometricWaitingSum p hp hp1)

end ECRuntime
