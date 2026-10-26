import ECRuntime.AdaptiveLeadingOnesMonotoneTrajectory
import ECRuntime.AEAbsorbingExpectedOccupation
import Mathlib

open scoped ENNReal
open MeasureTheory

namespace ECRuntime

/-!
Stage 295 (P01, proposed). Instantiate the generic almost-sure absorbing
hitting-time identity to the genuine adaptive LeadingOnes Markov chain.
Once Stage 288 and Stage 294 are certified, the remaining Stage-282
statement differs only by the exact optimum/score membership equivalence.
-/

/-- The adaptive LeadingOnes fixed-start expectation is the full countable
sum of the genuine probabilities of not yet being in the optimum target. -/
theorem proposed_leadingOnesAdaptive_fixedInitial_runtime_eq_survivalTsum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) :
    (∫⁻ path : Nat → BitString n,
      transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x) =
    ∑' t : Nat,
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          transitionTrajectoryState x path t ∉ leadingOnesTarget n} := by
  exact proposed_aeAbsorbing_expectedHitting_eq_survivalTsum
    (leadingOnesAdaptiveTransition rate)
    (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
    (leadingOnesTarget n) x
    (proposed_leadingOnesAdaptive_ae_optimumAbsorbing rate hrate x)

end ECRuntime
