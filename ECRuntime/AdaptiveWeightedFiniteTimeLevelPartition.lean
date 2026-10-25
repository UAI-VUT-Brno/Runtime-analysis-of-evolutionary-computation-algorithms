import ECRuntime.AdaptiveLeadingOnesFiniteLevelOccupationPartition
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: generalize the certified exact-level partition to a finite arbitrary
initial-weight profile, rather than only a uniform start. -/

/-- At a fixed trajectory time the weighted nonoptimal occupation mass
is precisely the weighted sum of disjoint exact-level occupation masses. -/
theorem proposed_leadingOnesAdaptive_weightedNonoptimalTimeMass_eq_levelSum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (initial : BitString n → ENNReal) (t : Nat) :
    (∑ x : BitString n,
      initial x * transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) < n}) =
    ∑ i : Fin n,
      ∑ x : BitString n,
        initial x * transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) = i.val} := by
  classical
  calc
    (∑ x : BitString n,
      initial x * transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) < n}) =
        ∑ x : BitString n,
          initial x * (∑ i : Fin n,
            transitionTrajectoryMeasure
              (leadingOnesAdaptiveTransition rate)
              (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
              {path : Nat → BitString n |
                leadingOnes (transitionTrajectoryState x path t) = i.val}) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [proposed_leadingOnesAdaptive_nonoptimalMass_eq_sumExactLevels
        n rate hrate x t]
    _ = ∑ x : BitString n, ∑ i : Fin n,
          initial x * transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
            {path : Nat → BitString n |
              leadingOnes (transitionTrajectoryState x path t) = i.val} := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = _ := Finset.sum_comm

end ECRuntime
