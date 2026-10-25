import ECRuntime.RLSStrictMonotoneFixedTargetExact
import ECRuntime.RLSFixedTargetUniformBinomialFormula
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 277 (P07, dependent research proposal). Promote the exact
uniform-start binomial/harmonic fixed-target runtime identity from
positive linear objectives to arbitrary coordinatewise strictly
monotone Boolean objectives. Stage 272 must first be certified.
-/

/-- Under any strictly coordinate-monotone objective, the uniform-start
RLS fixed-target mean is exactly the binomially weighted truncated
harmonic expression, without a linear-fitness assumption. -/
theorem proposed_strictMonotoneRLS_uniformFixedTarget_binomialRuntime
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (r : Nat) :
    ((Fintype.card (BitString n) : Real)⁻¹) *
      (∑ x : BitString n,
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          (rlsZeroAtMost (n := n) r) x).toReal) =
    ((Fintype.card (BitString n) : Real)⁻¹) *
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : Real) *
          (if k ≤ r then 0
           else (n : Real) * (harmonicReal k - harmonicReal r))) := by
  have hones : PositiveLinearWeights (fun _ : Fin n => (1 : Real)) := by
    intro i
    exact zero_lt_one
  rw [candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf]
  rw [← candidate_rls_linear_transition_eq_oneMax
    hn (fun _ : Fin n => (1 : Real)) hones]
  exact proposed_rlsLinear_fixedTarget_uniformBinomialRuntime
    hn (fun _ : Fin n => (1 : Real)) hones r

end ECRuntime
