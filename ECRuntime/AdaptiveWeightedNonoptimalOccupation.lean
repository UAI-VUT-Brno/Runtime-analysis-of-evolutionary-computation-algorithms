import ECRuntime.AdaptiveLeadingOnesCountableOccupationBridge
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-! P01: extend the genuine fixed-initial occupation identity to an
arbitrary (possibly nonuniform) nonnegative initial mass on bit strings.
This is not yet the geometric level-residence factorization in Stage 245. -/

/-- Finite initial mixtures preserve the true countable occupation identity;
this result has no assumption that the expected runtime is finite. -/
theorem proposed_leadingOnesAdaptive_weightedPathExpected_eq_occupation
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (weight : BitString n → ENNReal) :
    (∑ x : BitString n, weight x *
      ∫⁻ path : Nat → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
        ∂transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x) =
    ∑ x : BitString n, weight x *
      ∑' t : Nat,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) < n} := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  rw [proposed_leadingOnesAdaptive_fixedInitial_runtime_eq_nonoptimalOccupation
    n rate hrate x]

end ECRuntime
