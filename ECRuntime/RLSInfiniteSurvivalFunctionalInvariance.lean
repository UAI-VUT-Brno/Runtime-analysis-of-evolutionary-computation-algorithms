import ECRuntime.RLSMonotoneFixedTargetSurvivalInvariant
import Mathlib

open scoped ENNReal
namespace ECRuntime

/-! Stage 306 (P02). A genuinely infinite-horizon nonnegative survival
functional, allowing non-summable costs and infinite values. Termwise
invariance is already provided by the certified strict-monotonicity lemma;
Mathlib's `tsum_congr` avoids a gratuitous summability hypothesis. -/

/-- Every nonnegative time-cost profile gives the same extended survival
functional on two strictly coordinate-monotone RLS objectives. -/
theorem proposed_strictMonotoneRLS_infiniteSurvivalFunctional_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r : Nat) (x : BitString n) (cost : Nat → ENNReal) :
    (∑' t : Nat, cost t * ENNReal.ofReal
      (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        (rlsZeroAtMost (n := n) r)ᶜ t x)) =
    (∑' t : Nat, cost t * ENNReal.ofReal
      (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        (rlsZeroAtMost (n := n) r)ᶜ t x)) := by
  apply tsum_congr
  intro t
  rw [proposed_strictMonotoneRLS_fixedTarget_survival_objectiveInvariant
    hn fitness₁ fitness₂ hf₁ hf₂ r t x]

end ECRuntime
