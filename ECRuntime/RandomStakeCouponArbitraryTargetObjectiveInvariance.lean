import ECRuntime.RandomStakeCouponArbitraryTargetRuntime
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: the full law of coupon collection is objective-independent under
strict coordinate monotonicity, even for an arbitrary, non-monotone target. -/

/-- Two strictly coordinate-monotone RLS objectives induce equal expected
hitting times for every target and every starting bit string. -/
theorem proposed_strictMonotoneRLS_arbitraryTarget_runtime_fitnessInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (target : Set (BitString n)) (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
      target x =
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
      target x := by
  rw [← proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS
        hn fitness₁ hf₁ target x,
      ← proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS
        hn fitness₂ hf₂ target x]

end ECRuntime
