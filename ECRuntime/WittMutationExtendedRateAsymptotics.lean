import ECRuntime.WittMutationExtendedRuntime
import ECRuntime.WittMutationRateAsymptotics
import Mathlib

open scoped BigOperators ENNReal
open Filter
open Asymptotics

namespace ECRuntime

/-!
# Stage 51: fixed-scale rate asymptotics beyond the first certified interval

Stage 46 proved the exact singleton-rate asymptotics under the historical hypothesis
`c <= 1`.  That restriction was convenient for the finite proof at the time, but it is
not intrinsic to the fixed-`c` limit.  Stage 50 has meanwhile propagated the finite Witt
runtime theorem to the larger compiler-promoted interval `0 < c <= 21/20`.

This module removes the obsolete asymptotic restriction without changing the promoted
Stage 46 source.  For every fixed real `c` it proves

`(1-c/n)^(n-1) -> exp(-c)`

and

`n * q_n(c) -> c * exp(-c)`,

where `q_n(c) = (c/n)(1-c/n)^(n-1)`.  For every fixed `c > 0`, inversion gives

`(n q_n(c))^(-1) -> exp(c)/c`.

The only additional proof idea is to avoid requiring `1-c/n != 0` uniformly at a fixed
small dimension.  In the quotient identity used to lower the exponent from `n` to
`n-1`, the exceptional case `1-c/n = 0` is handled directly for `n >= 2`; otherwise the
usual field cancellation applies.

The module also names the exact-rate Stage-50 expectation envelope.  Thus the finite
runtime theorem on the full certified interval is explicitly attached to the same
singleton rate whose normalized inverse converges to `exp(c)/c`.  No C2/C3, drift, or
tail argument is modified here.
-/

/-- For every fixed real `c`, the survival factor with exponent `n-1` converges to
`exp(-c)`.  No finite-scale restriction on `c` is needed for this asymptotic statement. -/
theorem scaledMutation_survival_pow_pred_tendsto_exp_neg_fixed
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (1 - scaledMutationRate c n) ^ (n - 1))
      Filter.atTop (nhds (Real.exp (-c))) := by
  have hraw :
      Filter.Tendsto
        (fun n : ℕ => (1 - c / (n : ℝ)) ^ n)
        Filter.atTop (nhds (Real.exp (-c))) := by
    simpa [sub_eq_add_neg, neg_div] using
      (Real.tendsto_one_add_div_pow_exp (-c))
  have hpow :
      Filter.Tendsto
        (fun n : ℕ => (1 - scaledMutationRate c n) ^ n)
        Filter.atTop (nhds (Real.exp (-c))) := by
    apply hraw.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    rw [scaledMutationRate_eq_div_of_pos hn]
  have hbase :
      Filter.Tendsto
        (fun n : ℕ => 1 - scaledMutationRate c n)
        Filter.atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds.sub (scaledMutationRate_tendsto_zero c))
  have hquot :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 - scaledMutationRate c n) ^ n /
            (1 - scaledMutationRate c n))
        Filter.atTop (nhds (Real.exp (-c))) := by
    simpa only [Pi.div_def, div_one] using
      hpow.div hbase (by norm_num : (1 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  by_cases hsurv : 1 - scaledMutationRate c n = 0
  · have hnne : n ≠ 0 := by omega
    have hpredne : n - 1 ≠ 0 := by omega
    simp [hsurv, hnne, hpredne]
  · apply (div_eq_iff hsurv).2
    rw [← pow_succ]
    congr 1
    omega

/-- For every fixed real scale, the exact singleton rate has normalized limit
`c * exp(-c)`. -/
theorem nat_mul_scaledLinearSingletonRate_tendsto_fixed
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * scaledLinearSingletonRate c n)
      Filter.atTop (nhds (c * Real.exp (-c))) := by
  have hsurv := scaledMutation_survival_pow_pred_tendsto_exp_neg_fixed c
  have hmul :
      Filter.Tendsto
        (fun n : ℕ => c * (1 - scaledMutationRate c n) ^ (n - 1))
        Filter.atTop (nhds (c * Real.exp (-c))) :=
    hsurv.const_mul c
  apply hmul.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  unfold scaledLinearSingletonRate linearSingletonRate
  rw [scaledMutationRate_eq_div_of_pos hn]
  field_simp [hnR]

/-- For every fixed positive scale, the normalized inverse singleton rate converges to
`exp(c)/c`.  In particular this applies throughout the enlarged Stage-49 certified
interval `0 < c <= 21/20`. -/
theorem normalized_inverse_scaledLinearSingletonRate_tendsto_leadingFactor_fixed
    {c : ℝ} (hc0 : 0 < c) :
    Filter.Tendsto
      (fun n : ℕ => (((n : ℝ) * scaledLinearSingletonRate c n)⁻¹))
      Filter.atTop (nhds (wittMutationLeadingRuntimeFactor c)) := by
  have hrate := nat_mul_scaledLinearSingletonRate_tendsto_fixed c
  have hlimpos : 0 < c * Real.exp (-c) :=
    mul_pos hc0 (Real.exp_pos (-c))
  have hinv := hrate.inv₀ hlimpos.ne'
  have hfactor :
      (c * Real.exp (-c))⁻¹ = wittMutationLeadingRuntimeFactor c := by
    unfold wittMutationLeadingRuntimeFactor
    rw [Real.exp_neg]
    field_simp [hc0.ne', Real.exp_ne_zero]
  simpa [hfactor] using hinv

/-- Named exact-rate expectation envelope used by the Stage-50 certified-regime theorem. -/
noncomputable def wittMutationExactRateRuntimeUpperBound
    (c : ℝ) (n : ℕ) : ℝ :=
  (scaledLinearSingletonRate c n)⁻¹ *
    (1 + Real.log 3 + Real.log (n : ℝ))

/-- The Stage-50 finite expectation theorem factors through the exact singleton rate
before the conservative `3/c` estimate is applied. -/
theorem wittMutation_runtimeSup_le_exactRate_upperBound_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (wittMutationExactRateRuntimeUpperBound c n) := by
  have hcert :=
    wittMutation_runtimeSup_le_certificate_scaled_of_le_certifiedScale
      hn hc0 hc w hw hmono x
  have hmult :=
    wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_certifiedScale
      hn hc0 hc w x
  unfold wittMutationExactRateRuntimeUpperBound
  exact hcert.trans (ENNReal.ofReal_le_ofReal hmult)

/-- The sharp fixed-scale inverse-rate factor remains globally minimized at `c=1`, so
this optimizer statement automatically covers the enlarged certified interval. -/
theorem wittMutationLeadingRuntimeFactor_one_le_fixed
    {c : ℝ} (hc0 : 0 < c) :
    wittMutationLeadingRuntimeFactor 1 ≤
      wittMutationLeadingRuntimeFactor c := by
  exact wittMutationLeadingRuntimeFactor_minimized_at_one hc0

end ECRuntime
