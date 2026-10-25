import ECRuntime.StrictMonotoneRLS
import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 167 candidate: uniform-start RLS on strictly monotone functions

Source direction: Doerr--Doerr, *Collecting Coupons with Random Initial Stake*,
Theorem 2 in the 2013 preprint, restricted to one-bit RLS and the precise
coordinatewise-strict monotonicity predicate already formalized in
`StrictMonotoneRLSKernelSupport`.

The transition-kernel reduction and deterministic-start harmonic mean already
exist in the certified library. The remaining task is to carry their equality
through uniform averaging and the exact binomial/harmonic transform.

The user approved the theorem statement after the first candidate build. The
proof is now proposed for compiler verification, axiom inspection, and promotion
gates; no verification or promotion is claimed merely from this source file.
-/

/-- Uniformly averaged number of one-bit RLS mutation iterations needed to
reach `allOnes` on a given fitness function. The initial fitness evaluation is
not counted. The definition makes no claim that the supplied kernel converges. -/
noncomputable def strictMonotoneRLSUniformInitialMean
    {n : ℕ} (hn : 0 < n) (fitness : BitString n → ℝ) : ℝ :=
  (Finset.univ.sum (fun x : BitString n =>
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : ℝ) ^ n

/-- Concrete non-vacuity witness: standard OneMax fitness meets the
strict coordinate-monotonicity hypothesis in dimension one. -/
example : CandidateCoordinateStrictMonotonicity (oneMaxReal (n := 1)) := by
  intro x i hi
  change (oneMax x : ℝ) <
    (oneMax (mutateWithMask x ({i} : MutationMask 1)) : ℝ)
  exact_mod_cast oneMax_single_zero_flip_improves x i hi

/-- Proposed full-uniform-start monotone RLS mean identity. It is stronger
in objective scope than the currently public positive-linear identity,
but does not assert any other algorithmic result from the source paper. -/
theorem proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection
    {n : ℕ} (hn : 0 < n)
    (fitness : BitString n → ℝ)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    strictMonotoneRLSUniformInitialMean hn fitness =
      (n : ℝ) *
        (harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : ℝ) / ((j : ℝ) * (2 : ℝ) ^ j))) := by
  classical
  unfold strictMonotoneRLSUniformInitialMean
  have hsum :
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          ({allOnes n} : Set (BitString n)) x).toReal)) =
        Finset.univ.sum (fun x : BitString n =>
          (n : ℝ) * harmonicReal (zeroCount x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [candidateStrictMonotoneRLS_runtimeSup_eq_harmonic hn fitness hf x]
    exact ENNReal.toReal_ofReal
      (mul_nonneg (Nat.cast_nonneg n) (harmonicReal_nonneg (zeroCount x)))
  rw [hsum]
  calc
    ((Finset.univ.sum (fun x : BitString n =>
        (n : ℝ) * harmonicReal (zeroCount x))) / (2 : ℝ) ^ n) =
      ((n : ℝ) / (2 : ℝ) ^ n) *
        (Finset.sum (Finset.range (n + 1)) (fun k =>
          (Nat.choose n k : ℝ) * harmonicReal k)) := by
            exact rlsLinear_uniformInitial_harmonic_average n
    _ = (n : ℝ) *
          (harmonicReal n -
            (Finset.Icc 1 n).sum (fun j =>
              (1 : ℝ) / ((j : ℝ) * (2 : ℝ) ^ j))) := by
            rw [← proposed_binomialHarmonicAverage_closedForm n]
            ring

end ECRuntime
