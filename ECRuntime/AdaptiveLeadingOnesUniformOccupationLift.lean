import ECRuntime.AdaptiveLeadingOnesCountableOccupationBridge
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime
/-! P01. Lift the true first-hitting occupation identity from individual
initial states to the uniform starting law; unlike a residence surrogate,
this identity refers to the genuine path-measure integral. -/
/-- Lift fixed-start genuine occupation identities to a finite uniform mixture. -/
theorem proposed_leadingOnesAdaptive_uniformPathExpected_eq_uniformOccupation
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1) :
    (∑ x : BitString n,
      ∫⁻ path : Nat → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
        ∂transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x) =
    ∑ x : BitString n,
      ∑' t : Nat,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) < n} := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  exact proposed_leadingOnesAdaptive_fixedInitial_runtime_eq_nonoptimalOccupation
    n rate hrate x
end ECRuntime
