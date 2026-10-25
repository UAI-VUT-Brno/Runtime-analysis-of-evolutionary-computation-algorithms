import ECRuntime.StrictMonotoneRLS
import ECRuntime.RLSUniformInitialCouponSurvivalInclusionExclusion
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 170 approved statement: exact survival law for monotone fitness

Doerr--Doerr (2013) uses a coupon-collector process; the certified Stage166
finite survival distribution assumes positive *linear* weights. At the RLS
kernel level, strictly coordinate-monotone objectives are already proved
equivalent to OneMax. This proposed claim transports the certified identity
without introducing independence assumptions or re-proving inclusion-exclusion.

User approval was given after the Stage 167–169 proof-1 verification.
The proof and exact statement header are unchanged; public integration still
requires the official verification and axiom gates.
-/

/-- Proposed finite-time uniform-start coupon survival probability for every
strictly coordinate-monotone objective under one-bit RLS. -/
theorem proposed_strictMonotoneRLS_uniformInitial_couponSurvival
    {n : ℕ} (hn : 0 < n) (fitness : BitString n → ℝ)
    (hf : CandidateCoordinateStrictMonotonicity fitness) (t : ℕ) :
    (Finset.univ.sum (fun x : BitString n =>
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        ({allOnes n} : Set (BitString n))ᶜ t x)) / (2 : ℝ) ^ n =
      (Finset.Icc (1 : ℕ) n).sum (fun j =>
        (-1 : ℝ) ^ (j + 1) * (Nat.choose n j : ℝ) /
          (2 : ℝ) ^ j *
          (1 - (j : ℝ) / (n : ℝ)) ^ t) := by
  classical
  have hw : PositiveLinearWeights (fun _ : Fin n => (1 : ℝ)) := by
    intro i
    norm_num
  have hmono := candidateStrictMonotoneRLS_transition_eq_oneMax
    hn fitness hf
  have hlinear := candidate_rls_linear_transition_eq_oneMax hn
    (fun _ : Fin n => (1 : ℝ)) hw
  rw [hmono, ← hlinear]
  exact proposed_rlsLinear_uniformInitial_couponSurvival_inclusionExclusion
    hn (fun _ : Fin n => (1 : ℝ)) hw t

end ECRuntime
