import ECRuntime.WittMutationStrictTail
import ECRuntime.MutationRateAsymptotics
import Mathlib

namespace ECRuntime

/-!
# Stage 46: asymptotics of the parameterized Witt singleton drift rate

Stage 45 closes the finite one-step Witt drift proof for the scaled mutation regime
`p = c/n` on the first formally verified interval `0 <= c <= 1`, `n >= 4`.  The exact
multiplicative-drift coefficient is

`linearSingletonRate n p = p * (1-p)^(n-1)`.

This module isolates the asymptotic algebra needed to read off the fixed-`c` leading
runtime factor.  For fixed `c <= 1`, it proves

`(1-c/n)^(n-1) -> exp(-c)`

and hence

`n * linearSingletonRate n (c/n) -> c * exp(-c)`.

For `c > 0` the inverse normalized rate therefore converges to `exp(c)/c`.  The module
also proves directly that this leading factor is minimized at `c = 1` among all positive
real `c`.  No new stochastic argument is introduced here; the finite drift theorem remains
exactly the compiler-promoted Stage-45 result.
-/

/-- The exact singleton drift coefficient in the scaled mutation regime `p=c/n`. -/
noncomputable def scaledLinearSingletonRate (c : ℝ) (n : ℕ) : ℝ :=
  linearSingletonRate n (scaledMutationRate c n)

/-- The fixed-`c` leading factor obtained by inverting the asymptotic singleton rate. -/
noncomputable def wittMutationLeadingRuntimeFactor (c : ℝ) : ℝ :=
  Real.exp c / c

/-- For fixed `c <= 1`, the survival factor with exponent `n-1` converges to `exp(-c)`.
The upper bound on `c` is chosen to match the currently verified finite drift regime and
also gives an elementary eventual nonvanishing proof for the survival factor. -/
theorem scaledMutation_survival_pow_pred_tendsto_exp_neg
    {c : ℝ} (hc1 : c ≤ 1) :
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
  have hnpos : 0 < n := by omega
  have hcn : c < (n : ℝ) := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hp1 : scaledMutationRate c n < 1 :=
    scaledMutationRate_lt_one hnpos hcn
  have hsurv : 1 - scaledMutationRate c n ≠ 0 :=
    (sub_pos.mpr hp1).ne'
  apply (div_eq_iff hsurv).2
  rw [← pow_succ]
  congr 1
  omega

/-- The exact scaled singleton rate has normalized limit `c * exp(-c)`. -/
theorem nat_mul_scaledLinearSingletonRate_tendsto
    {c : ℝ} (hc1 : c ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * scaledLinearSingletonRate c n)
      Filter.atTop (nhds (c * Real.exp (-c))) := by
  have hsurv := scaledMutation_survival_pow_pred_tendsto_exp_neg (c := c) hc1
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

/-- For positive fixed `c`, the inverse normalized singleton rate converges to the
leading runtime factor `exp(c)/c`. -/
theorem normalized_inverse_scaledLinearSingletonRate_tendsto_leadingFactor
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ =>
        (((n : ℝ) * scaledLinearSingletonRate c n)⁻¹))
      Filter.atTop (nhds (wittMutationLeadingRuntimeFactor c)) := by
  have hrate := nat_mul_scaledLinearSingletonRate_tendsto (c := c) hc1
  have hlimpos : 0 < c * Real.exp (-c) :=
    mul_pos hc0 (Real.exp_pos (-c))
  have hinv := hrate.inv₀ hlimpos.ne'
  have hfactor :
      (c * Real.exp (-c))⁻¹ = wittMutationLeadingRuntimeFactor c := by
    unfold wittMutationLeadingRuntimeFactor
    rw [Real.exp_neg]
    field_simp [hc0.ne', Real.exp_ne_zero]
  simpa [hfactor] using hinv

@[simp] theorem wittMutationLeadingRuntimeFactor_one :
    wittMutationLeadingRuntimeFactor 1 = Real.exp 1 := by
  simp [wittMutationLeadingRuntimeFactor]

/-- The leading inverse-rate factor is never below its value at `c=1`. -/
theorem wittMutationLeadingRuntimeFactor_one_le
    {c : ℝ} (hc0 : 0 < c) :
    Real.exp 1 ≤ wittMutationLeadingRuntimeFactor c := by
  unfold wittMutationLeadingRuntimeFactor
  rw [le_div_iff₀ hc0]
  have hcExp : c ≤ Real.exp (c - 1) := by
    have h := Real.add_one_le_exp (c - 1)
    linarith
  calc
    Real.exp 1 * c ≤ Real.exp 1 * Real.exp (c - 1) :=
      mul_le_mul_of_nonneg_left hcExp (Real.exp_pos 1).le
    _ = Real.exp c := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Consequently `c=1` is a global minimizer of the fixed-`c` leading runtime factor on
positive mutation scales. -/
theorem wittMutationLeadingRuntimeFactor_minimized_at_one
    {c : ℝ} (hc0 : 0 < c) :
    wittMutationLeadingRuntimeFactor 1 ≤
      wittMutationLeadingRuntimeFactor c := by
  rw [wittMutationLeadingRuntimeFactor_one]
  exact wittMutationLeadingRuntimeFactor_one_le hc0

end ECRuntime
