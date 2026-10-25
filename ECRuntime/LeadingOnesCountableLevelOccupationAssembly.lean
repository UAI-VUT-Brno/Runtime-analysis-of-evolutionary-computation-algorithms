import ECRuntime.AdaptiveLeadingOnesFiniteLevelOccupationPartition
import ECRuntime.ENNRealTimeLevelTsumInterchange
import ECRuntime.AdaptiveLeadingOnesUniformFiniteTimeLevelPartition
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: countable expected nonoptimal occupation is the sum of actual
expected exact-level occupation times, without changing the state model or
assuming termination. Dependency chain: Stage 304, 308, 311. -/

/-- Sum the genuine uniform-initialization finite-time level partition over
all times, with no exchange of an unbounded real series. -/
theorem proposed_leadingOnesAdaptive_uniformOccupation_eq_sumExactLevelOccupations
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1) :
    (∑' t : Nat,
      ∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) < n}) =
    ∑ i : Fin n,
      ∑' t : Nat,
        ∑ x : BitString n,
          transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
            {path : Nat → BitString n |
              leadingOnes (transitionTrajectoryState x path t) = i.val} := by
  classical
  calc
    _ = ∑' t : Nat,
          ∑ i : Fin n,
            ∑ x : BitString n,
              transitionTrajectoryMeasure
                (leadingOnesAdaptiveTransition rate)
                (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
                {path : Nat → BitString n |
                  leadingOnes (transitionTrajectoryState x path t) = i.val} := by
          apply tsum_congr
          intro t
          exact proposed_leadingOnesAdaptive_uniformNonoptimalTimeMass_eq_levelSum
            n rate hrate t
    _ = _ := proposed_ennreal_timeLevel_sum_swap
      (fun t i => ∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) = i.val})

end ECRuntime
