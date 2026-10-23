import ECRuntime.RLSFiniteSurvivalCouponBound
import ECRuntime.StrictMonotoneRLSKernelSupport
import ECRuntime.LevelExitTail
import Mathlib

namespace ECRuntime

/-!
Stage 132: user-approved statement; provisional public integration.
For every strictly coordinate-monotone fitness function, the RLS transition
kernel agrees with the OneMax kernel (Stage 119). The same finite-horizon
coupon-collector tail estimate should therefore transfer unchanged.
The monotonicity assumption is spelt out here rather than referencing
an unpromoted candidate-only definition.
-/

/-- RLS on every strictly coordinate-monotone Boolean landscape has
 the universal coupon-collector survival tail. -/
theorem proposed_strictMonotoneRLS_finiteSurvival_couponBound
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hmono : ∀ (x : BitString n) (i : Fin n), x i = false →
      fitness x < fitness (mutateWithMask x ({i} : MutationMask n)))
    (x : BitString n) (t : Nat) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n))ᶜ t x ≤
    (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t := by
  classical
  have hkernel := support_strictMonotoneRLS_transition_eq_oneMax
    hn fitness hmono
  rw [hkernel]
  have hbound := proposed_rlsOneMax_finiteSurvival_couponBound hn x t
  simpa only [← oneMaxTarget_eq_singleton n] using hbound

end ECRuntime
