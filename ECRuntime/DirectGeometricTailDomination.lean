import ECRuntime.PotentialRuntimeTailRecursion
import ECRuntime.GeometricCouplingDominationEndpoint
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 69: thin direct-domination endpoint

`PotentialRuntimeTailRecursion.lean` removes the adaptive coupling from the process side
of the Stage-26 theorem.  The only remaining distributional bridge for the new route is
now explicit: identify the recursively defined full-prefix comparison tail with the
natural-threshold tail of the already verified independent geometric-sum law.

This module packages that one missing theorem as a proposition and proves that it is
sufficient for natural-threshold stochastic domination of the actual zero-potential
hitting time.  Consequently a successful fix-69 build reduces the direct route to a
single geometric-sum identification problem, while the earlier coupling construction
remains available as a fallback.
-/

/-- Exact natural-threshold identification still required on the geometric side of the
direct proof. -/
def HasGeometricSumTailIdentification
    {m : Nat} (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1) : Prop :=
  forall k : Nat,
    runtimeTailMass
        (geometricWaitingSumMeasure
          (geometricLevelProbabilityVector p hp hp1))
        id (k : ENNReal) =
      ENNReal.ofReal (finiteGeometricComparisonTail p m k)

/-- Once the geometric-sum tail satisfies the recursive table, the direct Bellman/tail
argument immediately gives natural-threshold domination of the actual hitting time. -/
theorem natTailDominated_transitionTrajectoryPotentialHittingTime_geometricWaitingSum_of_identification
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : alpha)
    (hgeom : HasGeometricSumTailIdentification p hp hp1) :
    NatTailDominated
      (transitionTrajectoryMeasure P hP x)
      (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector p hp hp1)) id := by
  intro k
  calc
    runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
        (k : ENNReal) <=
      ENNReal.ofReal (finiteGeometricComparisonTail p m k) :=
        transitionTrajectoryPotentialHittingTime_tailMass_le_geometricComparisonTail
          P hP V hbound p (fun i => (hp i).le) hp1 hexit hmonoP x k
    _ = runtimeTailMass
        (geometricWaitingSumMeasure
          (geometricLevelProbabilityVector p hp hp1))
        id (k : ENNReal) := (hgeom k).symm

end ECRuntime
