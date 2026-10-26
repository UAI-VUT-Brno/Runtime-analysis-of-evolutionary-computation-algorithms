import ECRuntime.AdaptiveLeadingOnesAEFirstVisitEntry
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. The first-entry event and the two-coordinate below-to-exact
event have equal genuine path measure, by a.e. equivalence. To finish
Stage 329 the latter must still be identified with its *finite* path law. -/

/-- Genuine first-visit and below-to-exact probabilities agree at any
positive time, without claiming pointwise equality of their event sets. -/
theorem proposed_leadingOnesAdaptive_firstVisitSuccMass_eq_belowEntryMass
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
          ∀ s : Nat, s < t + 1 →
            leadingOnes (transitionTrajectoryState x path s) ≠ i.val} =
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) < i.val ∧
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val} := by
  apply measure_congr
  filter_upwards [proposed_leadingOnesAdaptive_ae_firstVisitSucc_iff_below
    rate hrate x i t] with path hiff
  exact propext hiff

end ECRuntime
