import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. Base case for a genuine first-entrance renewal: at time zero,
there is no previous trajectory state to exclude. -/

/-- Time-zero occupation and genuine first-visit events have the same mass. -/
theorem proposed_leadingOnesAdaptive_firstVisitAtZeroMass_eq_occupation
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path 0) = i.val ∧
        ∀ s : Nat, s < 0 →
          leadingOnes (transitionTrajectoryState x path s) ≠ i.val} =
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path 0) = i.val} := by
  congr 1
  ext path
  simp

end ECRuntime
