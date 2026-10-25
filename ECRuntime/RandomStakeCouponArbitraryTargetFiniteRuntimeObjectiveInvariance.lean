import ECRuntime.RandomStakeCouponArbitraryTargetFiniteRuntime
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: finite-horizon hitting-time comparison is identical for any two
strict coordinate-monotone objectives, even with arbitrary fixed target. -/

/-- Strict-monotone RLS finite-horizon expected hitting times are independent
of the objective for every target and every initial bit string. -/
theorem proposed_strictMonotoneRLS_arbitraryTarget_finiteRuntime_fitnessInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (target : Set (BitString n)) (t : Nat) (x : BitString n) :
    finiteHorizonRuntime
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
      target t x =
    finiteHorizonRuntime
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
      target t x := by
  rw [← proposed_couponProcess_arbitraryTarget_finiteRuntime_eq_strictMonotoneRLS
        hn fitness₁ hf₁ target t x,
      ← proposed_couponProcess_arbitraryTarget_finiteRuntime_eq_strictMonotoneRLS
        hn fitness₂ hf₂ target t x]

end ECRuntime
