import ECRuntime.WittMutationExtendedRateAsymptotics
import ECRuntime.AsymptoticRegime
import Mathlib

open scoped BigOperators ENNReal
open Filter
open Asymptotics

namespace ECRuntime

/-!
# Stage 52: sharp leading constant for the exact-rate certified runtime envelope

Stage 51 removes the historical `c <= 1` restriction from the fixed-scale singleton-rate
asymptotics.  In particular, for every fixed `c > 0`,

`((n : ℝ) * q_n(c))⁻¹ -> exp(c) / c`,

where `q_n(c) = scaledLinearSingletonRate c n`.

Stage 50 supplies the exact-rate runtime envelope on the compiler-certified finite interval
`0 < c <= 21/20`:

`q_n(c)⁻¹ * (1 + log 3 + log n)`.

This module connects those two facts.  The logarithmic prefactor satisfies

`(1 + log 3 + log n) / log n -> 1`,

so dividing the exact-rate envelope by `n log n` gives the sharp fixed-scale limit

`exp(c) / c`.

No drift, C2/C3, expectation, or tail argument is changed here.  The new theorem is a
pure asymptotic presentation layer over the Stage-50 finite runtime certificate and the
Stage-51 exact-rate asymptotics.
-/

/-- The exact-rate Stage-50 runtime envelope normalized by `n log n`. -/
noncomputable def wittMutationExactRateNormalizedRuntimeUpperBound
    (c : ℝ) (n : ℕ) : ℝ :=
  wittMutationExactRateRuntimeUpperBound c n / natLinearLogGrowth n

/-- The additive constant in the Stage-50 logarithmic factor disappears after division
by `log n`. -/
theorem wittMutation_log_prefactor_ratio_tendsto_one :
    Filter.Tendsto
      (fun n : ℕ =>
        (1 + Real.log 3 + Real.log (n : ℝ)) / Real.log (n : ℝ))
      Filter.atTop (nhds 1) := by
  have hlog :
      Filter.Tendsto
        (fun n : ℕ => Real.log (n : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto
        (fun n : ℕ => (Real.log (n : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hsmall :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 + Real.log 3) * (Real.log (n : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul (1 + Real.log 3)
  have hsum :
      Filter.Tendsto
        (fun n : ℕ =>
          1 + (1 + Real.log 3) * (Real.log (n : ℝ))⁻¹)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hsmall)
  apply hsum.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn1 : 1 < n := by omega
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlogne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hnR).ne'
  rw [add_div, div_self hlogne, div_eq_mul_inv]
  exact add_comm _ _

/-- For every fixed positive mutation scale, the normalized exact-rate runtime envelope
converges to the sharp leading coefficient `exp(c)/c`. -/
theorem wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_leadingFactor
    {c : ℝ} (hc0 : 0 < c) :
    Filter.Tendsto
      (fun n : ℕ => wittMutationExactRateNormalizedRuntimeUpperBound c n)
      Filter.atTop (nhds (wittMutationLeadingRuntimeFactor c)) := by
  have hrate :=
    normalized_inverse_scaledLinearSingletonRate_tendsto_leadingFactor_fixed hc0
  have hlog := wittMutation_log_prefactor_ratio_tendsto_one
  have hprod :
      Filter.Tendsto
        (fun n : ℕ =>
          (((n : ℝ) * scaledLinearSingletonRate c n)⁻¹) *
            ((1 + Real.log 3 + Real.log (n : ℝ)) / Real.log (n : ℝ)))
        Filter.atTop (nhds (wittMutationLeadingRuntimeFactor c)) := by
    simpa only [mul_one] using hrate.mul hlog
  apply hprod.congr'
  exact Filter.Eventually.of_forall (fun n => by
    unfold wittMutationExactRateNormalizedRuntimeUpperBound
      wittMutationExactRateRuntimeUpperBound natLinearLogGrowth
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring)

/-- Literature-facing specialization of the sharp normalized-envelope limit to the
compiler-certified mutation-scale interval. -/
theorem wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_certifiedScale
    {c : ℝ} (hc0 : 0 < c) (_hc : c ≤ wittMutationC3CertifiedScale) :
    Filter.Tendsto
      (fun n : ℕ => wittMutationExactRateNormalizedRuntimeUpperBound c n)
      Filter.atTop (nhds (wittMutationLeadingRuntimeFactor c)) := by
  exact wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_leadingFactor hc0

/-- On the certified interval, the finite Stage-50 runtime theorem is controlled by an
upper envelope whose normalized sharp leading coefficient is `exp(c)/c`. -/
theorem wittMutation_runtimeSup_le_sharpAsymptoticEnvelope_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (wittMutationExactRateRuntimeUpperBound c n) := by
  exact wittMutation_runtimeSup_le_exactRate_upperBound_certifiedScale
    hn hc0 hc w hw hmono x

/-- The sharp leading coefficient of the certified exact-rate envelope is minimized at
the standard scale `c = 1`. -/
theorem wittMutationExactRateRuntimeLeadingFactor_one_le_certifiedScale
    {c : ℝ} (hc0 : 0 < c) (_hc : c ≤ wittMutationC3CertifiedScale) :
    wittMutationLeadingRuntimeFactor 1 ≤
      wittMutationLeadingRuntimeFactor c := by
  exact wittMutationLeadingRuntimeFactor_one_le_fixed hc0

end ECRuntime
