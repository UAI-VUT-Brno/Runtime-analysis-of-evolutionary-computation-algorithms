import ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: finite-horizon target-survival invariance of strict-monotone RLS. -/

/-- Under strict coordinate monotonicity the entire finite-horizon survival
function is independent of the chosen objective, even for arbitrary targets. -/
theorem proposed_strictMonotoneRLS_arbitraryTarget_survival_fitnessInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (target : Set (BitString n)) (t : Nat) (x : BitString n) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
      targetᶜ t x =
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
      targetᶜ t x := by
  rw [← proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
        hn fitness₁ hf₁ target t x,
      ← proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
        hn fitness₂ hf₂ target t x]

end ECRuntime
