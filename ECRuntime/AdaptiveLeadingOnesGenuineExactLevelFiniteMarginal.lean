import ECRuntime.GenericFiniteCylinderMarginal
import ECRuntime.LeadingOnesExactStayBranch
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. Exact fixed-time level occupation is genuinely a finite marginal
of the infinite Ionescu--Tulcea trajectory, not a surrogate path weight.
This is the input to an eventual ENNReal one-step renewal theorem. -/

/-- The true infinite-path probability of visiting an exact LeadingOnes level
at any fixed time equals the explicitly weighted finite endpoint law. -/
theorem proposed_leadingOnesAdaptive_exactLevelMass_eq_finiteMarginal
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) = i.val} =
    finiteTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
      t x (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
  classical
  have hevent : MeasurableSet (leadingOnesFiniteScoreLevelAtHorizonSet x i t) :=
    (leadingOnesFiniteScoreLevelAtHorizonSet x i t).to_countable.measurableSet
  have heq :
      ({path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) = i.val} :
        Set (Nat → BitString n)) =
      (transitionTrajectoryTail t) ⁻¹'
        (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
    ext path
    change
      (leadingOnes (transitionTrajectoryState x path t) = i.val) ↔
      (leadingOnes (finiteTrajectoryEndpoint x t
        (transitionTrajectoryTail t path)) = i.val)
    rw [finiteTrajectoryEndpoint_transitionTrajectoryTail]
  rw [heq]
  exact proposed_transitionTrajectoryMeasure_finiteCylinder_eq_finiteMeasure
    (leadingOnesAdaptiveTransition rate)
    (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
    x t (leadingOnesFiniteScoreLevelAtHorizonSet x i t) hevent

end ECRuntime
