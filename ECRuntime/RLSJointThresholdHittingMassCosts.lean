import ECRuntime.RLSWeightedCountableHittingMass
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02. Simultaneous nonnegative initial-state, threshold, and time
mixtures of the RLS first-hit distribution remain invariant among
strictly coordinate-monotone objective functions. -/

/-- A finite family of different targets and time-cost profiles may be
combined without losing strict-monotone RLS objective invariance. -/
theorem proposed_strictMonotoneRLS_jointThresholdHittingMassCosts_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (R : Finset Nat) (thresholdWeight : Nat → ENNReal)
    (weight : BitString n → ENNReal) (cost : Nat → Nat → ENNReal) :
    (∑ r ∈ R, thresholdWeight r *
      ∑ x : BitString n, weight x *
        ∑' t : Nat, cost r t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
            (rlsZeroAtMost (n := n) r)ᶜ t x -
           finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
            (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) =
    (∑ r ∈ R, thresholdWeight r *
      ∑ x : BitString n, weight x *
        ∑' t : Nat, cost r t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
            (rlsZeroAtMost (n := n) r)ᶜ t x -
           finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
            (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) := by
  classical
  apply Finset.sum_congr rfl
  intro r _hr
  exact congrArg (fun z : ENNReal => thresholdWeight r * z)
    (proposed_strictMonotoneRLS_weightedCountableHittingMassCost_invariant
      hn fitness₁ fitness₂ hf₁ hf₂ r weight (cost r))

end ECRuntime
