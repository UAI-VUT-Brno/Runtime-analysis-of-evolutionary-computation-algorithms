import ECRuntime.RLSWeightedFixedTargetHittingMass
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 292 (P02, proposed). Objective invariance holds for *every* finite
linear statistic of the hitting-time mass, not only generating polynomials.
The conclusion does not assume weights or coefficients are nonnegative.
-/

/-- Every finitely supported signed linear statistic of weighted first-hit
masses is invariant across strictly monotone RLS objectives. -/
theorem proposed_strictMonotoneRLS_weightedHittingLinearStatistic_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (weights : BitString n → Real) (coeff : Nat → Real)
    (r T : Nat) :
    (∑ t ∈ Finset.range T, coeff t *
      ((∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ t x) -
       (∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x))) =
    (∑ t ∈ Finset.range T, coeff t *
      ((∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ t x) -
       (∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x))) := by
  apply Finset.sum_congr rfl
  intro t _ht
  rw [proposed_strictMonotoneRLS_weightedFixedTarget_hittingMass_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ weights r t]

end ECRuntime
