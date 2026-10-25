import ECRuntime.RLSCountableHittingMassCosts
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02. Pointwise first-hitting-time distribution invariance lifts to
arbitrary nonnegative start-distribution weights, without assuming finite
expected time or a summable cost profile. -/

/-- Nonnegative initial-state mixtures of countable first-hitting-time cost
functionals are invariant for one-bit RLS on strictly monotone objectives. -/
theorem proposed_strictMonotoneRLS_weightedCountableHittingMassCost_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r : Nat) (weight : BitString n → ENNReal) (cost : Nat → ENNReal) :
    (∑ x : BitString n, weight x *
      ∑' t : Nat, cost t * ENNReal.ofReal
        (finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ t x -
         finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) =
    (∑ x : BitString n, weight x *
      ∑' t : Nat, cost t * ENNReal.ofReal
        (finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ t x -
         finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) := by
  classical
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun z : ENNReal => weight x * z)
    (proposed_strictMonotoneRLS_countableHittingMassCost_invariant
      hn fitness₁ fitness₂ hf₁ hf₂ r x cost)

end ECRuntime
