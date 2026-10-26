import ECRuntime.RLSWeightedFixedTargetHittingMass
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 289 (P02). The entire finite generating polynomial of the
first-hitting distribution is invariant between strictly monotone
objectives. It refines equality of individual masses to a compact
functional identity, for arbitrary signed initial weights.
-/

/-- Weighted finite first-hitting-time generating polynomial. -/
noncomputable def proposed_RLSWeightedHittingPolynomial
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (weights : BitString n → Real) (r T : Nat) (z : Real) : Real :=
  ∑ t ∈ Finset.range T, z ^ t *
    ((∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        (rlsZeroAtMost (n := n) r)ᶜ t x) -
     (∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x))

/-- All finite Taylor coefficients, and thus the polynomial itself, agree. -/
theorem proposed_strictMonotoneRLS_weightedHittingPolynomial_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (weights : BitString n → Real) (r T : Nat) (z : Real) :
    proposed_RLSWeightedHittingPolynomial hn fitness₁ weights r T z =
      proposed_RLSWeightedHittingPolynomial hn fitness₂ weights r T z := by
  unfold proposed_RLSWeightedHittingPolynomial
  apply Finset.sum_congr rfl
  intro t _ht
  rw [proposed_strictMonotoneRLS_weightedFixedTarget_hittingMass_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ weights r t]

end ECRuntime
