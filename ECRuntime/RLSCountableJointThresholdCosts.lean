import ECRuntime.RLSJointThresholdHittingMassCosts
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02. A countable collection of objective-invariant joint target/time
cost functionals is invariant term by term; Mathlib's `tsum_congr` is sufficient.
No additional coupon-process assumption is introduced. -/

/-- Countably indexed collections of finite-threshold hitting-cost profiles
are invariant under replacement by another strictly monotone objective. -/
theorem proposed_strictMonotoneRLS_countableJointThresholdCosts_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (family : Nat → Finset Nat) (familyWeight : Nat → ENNReal)
    (thresholdWeight : Nat → ENNReal)
    (weight : BitString n → ENNReal) (cost : Nat → Nat → ENNReal) :
    (∑' j : Nat, familyWeight j *
       ∑ r ∈ family j, thresholdWeight r *
         ∑ x : BitString n, weight x *
           ∑' t : Nat, cost r t * ENNReal.ofReal
             (finiteLevelSurvival
               ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
               (rlsZeroAtMost (n := n) r)ᶜ t x -
              finiteLevelSurvival
               ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
               (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) =
    (∑' j : Nat, familyWeight j *
       ∑ r ∈ family j, thresholdWeight r *
         ∑ x : BitString n, weight x *
           ∑' t : Nat, cost r t * ENNReal.ofReal
             (finiteLevelSurvival
               ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
               (rlsZeroAtMost (n := n) r)ᶜ t x -
              finiteLevelSurvival
               ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
               (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) := by
  apply tsum_congr
  intro j
  exact congrArg (fun z : ENNReal => familyWeight j * z)
    (proposed_strictMonotoneRLS_jointThresholdHittingMassCosts_invariant
      hn fitness₁ fitness₂ hf₁ hf₂ (family j) thresholdWeight weight cost)

end ECRuntime
