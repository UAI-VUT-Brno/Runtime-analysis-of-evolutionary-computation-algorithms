import ECRuntime.AdaptiveWeightedFiniteTimeLevelPartition
import ECRuntime.ENNRealTimeLevelTsumInterchange
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: the genuine countable occupation identity extends beyond the uniform
initial population to arbitrary (unnormalized) finite state weights. -/

/-- An arbitrary nonnegative initial profile commutes with the exact-level
partition of the countable nonoptimal occupation measure. -/
theorem proposed_leadingOnesAdaptive_weightedOccupation_eq_exactLevelTsum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (initial : BitString n → ENNReal) :
    (∑' t : Nat,
      ∑ x : BitString n,
        initial x * transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) < n}) =
    ∑ i : Fin n,
      ∑' t : Nat,
        ∑ x : BitString n,
          initial x * transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
            {path : Nat → BitString n |
              leadingOnes (transitionTrajectoryState x path t) = i.val} := by
  classical
  calc
    _ = ∑' t : Nat, ∑ i : Fin n,
          ∑ x : BitString n,
            initial x * transitionTrajectoryMeasure
              (leadingOnesAdaptiveTransition rate)
              (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
              {path : Nat → BitString n |
                leadingOnes (transitionTrajectoryState x path t) = i.val} := by
      apply tsum_congr
      intro t
      exact proposed_leadingOnesAdaptive_weightedNonoptimalTimeMass_eq_levelSum
        n rate hrate initial t
    _ = _ := proposed_ennreal_timeLevel_sum_swap (fun t i =>
      ∑ x : BitString n,
        initial x * transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) = i.val})

end ECRuntime
