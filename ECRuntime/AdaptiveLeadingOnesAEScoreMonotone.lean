import ECRuntime.AdaptiveLeadingOnesMonotoneTrajectory
import ECRuntime.LeadingOnesExactEntryStep
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. Unlike pointwise monotonicity, this genuine-path score monotonicity
holds only almost surely. It follows from the previously certified
nonincreasing-potential support theorem, not from a new probabilistic axiom. -/

/-- The genuine adaptive LeadingOnes score is nondecreasing almost surely
at all pairs of times under a bounded state-dependent mutation schedule. -/
theorem proposed_leadingOnesAdaptive_ae_scoreMonotone
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) :
    ∀ᵐ path ∂transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x,
      Monotone (fun t =>
        leadingOnes (transitionTrajectoryState x path t)) := by
  filter_upwards [proposed_leadingOnesAdaptive_ae_potentialNonincreasing
    rate hrate x] with path hmono
  intro a b hab
  exact leadingOnes_score_nondecreasingAlong_of_potential
    x path hmono hab

end ECRuntime
