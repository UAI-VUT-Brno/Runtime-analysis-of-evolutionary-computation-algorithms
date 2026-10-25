import ECRuntime.LeadingOnes
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02 journal-extension frontier. The 2016 Algorithmica article
also investigates random initialization for LeadingOnes under the
(1+1)-EA; its claims are not consequences of the 2013 RLS theorem.
This records the real algorithm/initialization interface. -/

/-- A first source-specific target for the 2016 journal extension:
identify the uniformly averaged genuine LeadingOnes hitting-time
expectation with its finite-state Bellman runtime. -/
theorem proposed_P02_journal_leadingOnesEA_uniformMean_eq_runtimeSup
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ x : BitString n,
      ∫⁻ path : Nat → BitString n,
        transitionTrajectoryFirstHittingTime ({allOnes n} : Set (BitString n)) x path
        ∂transitionTrajectoryMeasure
          (onePlusOneTransition p (leadingOnesReal (n := n)))
          (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))) x) =
      ∑ x : BitString n,
        runtimeSup (onePlusOneTransition p (leadingOnesReal (n := n)))
          ({allOnes n} : Set (BitString n)) x := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  exact transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
    (onePlusOneTransition p (leadingOnesReal (n := n)))
    ({allOnes n} : Set (BitString n))
    (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))) x

end ECRuntime
