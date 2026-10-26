import ECRuntime.RLSWeightedHittingLinearStatistic
import Mathlib

open scoped BigOperators
namespace ECRuntime
/-! P02. Finite polynomial moments of first-hitting masses are exactly
objective-invariant, including signed start weights. -/
/-- Finite weighted hitting-time moments are independent of the strictly monotone objective. -/
theorem proposed_strictMonotoneRLS_weightedHittingMoment_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (weights : BitString n → Real) (power r T : Nat) :
    (∑ t ∈ Finset.range T, (t : Real) ^ power *
      ((∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ t x) -
       (∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x))) =
    (∑ t ∈ Finset.range T, (t : Real) ^ power *
      ((∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ t x) -
       (∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x))) := by
  exact proposed_strictMonotoneRLS_weightedHittingLinearStatistic_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ weights (fun t => (t : Real) ^ power) r T
end ECRuntime
