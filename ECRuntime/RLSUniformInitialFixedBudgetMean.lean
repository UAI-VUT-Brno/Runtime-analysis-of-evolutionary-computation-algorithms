import ECRuntime.RLSFixedBudget
import ECRuntime.UniformStartZeroCountMean
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 140 — provisional public promotion preparation (Round 24).
An exact finite-budget counterpart to the uniform-start coupon
bounds for RLS on positive linear objectives. It follows by averaging the
certified conditional fixed-budget mean (Stage 115) and the uniform-start
zero-count identity (Stage 136, promoted after Round 22).

Literature direction: Doerr--Doerr (2013), collecting coupons with random
initial stake. This is a first-moment statement only, not a tail-distribution
formula and not a theorem asserted by the original paper verbatim.
-/

/-- Averaged over uniformly weighted initial bitstrings, the expected
number of zeros remaining after t one-bit RLS mutations is exactly
(n/2)·(1-1/n)^t. Each finite trajectory uses its genuine transition weight. -/
theorem proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (t : Nat) :
    (Finset.univ.sum (fun x : BitString n =>
      Finset.univ.sum (fun path : FiniteTrajectory (BitString n) t =>
        finiteTrajectoryWeight
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w)) t x path *
          (zeroCount (finiteBudgetTerminal t x path) : Real)))) /
        (2 : Real) ^ n =
      ((n : Real) / 2) * (1 - 1 / (n : Real)) ^ t := by
  classical
  have hconditional :
      (Finset.univ.sum (fun x : BitString n =>
        Finset.univ.sum (fun path : FiniteTrajectory (BitString n) t =>
          finiteTrajectoryWeight
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
              (linearFitness w)) t x path *
            (zeroCount (finiteBudgetTerminal t x path) : Real)))) =
        Finset.univ.sum (fun x : BitString n =>
          (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t) := by
    apply Finset.sum_congr rfl
    intro x _
    exact rlsLinear_fixedBudget_expectedZeros_eq hn w hw x t
  rw [hconditional, ← Finset.sum_mul]
  have hmean := proposed_bitStrings_uniformAverage_zeroCount_eq_half n
  calc
    (∑ x : BitString n, (zeroCount x : Real)) *
        (1 - 1 / (n : Real)) ^ t / (2 : Real) ^ n =
      ((∑ x : BitString n, (zeroCount x : Real)) / (2 : Real) ^ n) *
        (1 - 1 / (n : Real)) ^ t := by ring
    _ = ((n : Real) / 2) * (1 - 1 / (n : Real)) ^ t := by rw [hmean]

end ECRuntime
