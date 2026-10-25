import ECRuntime.RLSFixedTargetHittingMassInvariance
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-! P02. The certified pointwise first-hit distributional identity implies
invariance of every nonnegative countable cost functional of the first-hit
mass. `ENNReal` avoids requiring artificial summability assumptions. -/

/-- Any nonnegative cost of the first-hitting-time probability mass, represented
by successive survival differences, is objective-independent for one-bit RLS
on strictly coordinate-monotone functions. -/
theorem proposed_strictMonotoneRLS_countableHittingMassCost_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r : Nat) (x : BitString n) (cost : Nat → ENNReal) :
    (∑' t : Nat, cost t * ENNReal.ofReal
      (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        (rlsZeroAtMost (n := n) r)ᶜ t x -
       finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) =
    (∑' t : Nat, cost t * ENNReal.ofReal
      (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        (rlsZeroAtMost (n := n) r)ᶜ t x -
       finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) := by
  classical
  apply tsum_congr
  intro t
  rw [proposed_strictMonotoneRLS_fixedTarget_hittingMass_objectiveInvariant
    hn fitness₁ fitness₂ hf₁ hf₂ r t x]

end ECRuntime
