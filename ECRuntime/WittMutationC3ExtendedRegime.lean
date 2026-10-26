import ECRuntime.WittMutationC3Envelope
import ECRuntime.WittMutationStrictTail
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 49 compatibility certificate: `c <= 21/20`

This retained module provides the first compiler-promoted finite extension of the scaled
Witt C3 branch beyond `c = 1`.  Endpoint-independent monotonicity now lives in
`WittMutationC3Envelope`; this file is only responsible for the numerical endpoint

`c_* = 21/20`.

For `4 <= n <= 8` the endpoint is checked exactly.  For `n >= 9`, the reciprocal-survival
power is bounded by `exp(56/53)` and then by explicit rational estimates.  The resulting
endpoint certificate is extended downward by the generic C3-envelope API.  This module is
retained because later asymptotic/runtime compatibility theorems use its public names.
-/

/-- Conservative Stage-49 scale used to obtain a uniform finite extension beyond one. -/
noncomputable def wittMutationC3CertifiedScale : ℝ := 21 / 20

@[simp] theorem wittMutationC3CertifiedScale_eq :
    wittMutationC3CertifiedScale = (21 / 20 : ℝ) := by
  rfl

/-- At the certified endpoint `c = 21/20`, the exact Stage-44 C3 envelope holds in every
`n >= 4`. -/
theorem wittMutationC3EnvelopeCondition_scaled_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) :
    WittMutationC3EnvelopeCondition
      (scaledMutationRate wittMutationC3CertifiedScale n) n := by
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hC_lt_n : wittMutationC3CertifiedScale < (n : ℝ) := by
    have hC4 : wittMutationC3CertifiedScale < (4 : ℝ) := by
      norm_num [wittMutationC3CertifiedScale]
    exact hC4.trans_le hn4
  have hp1 : scaledMutationRate wittMutationC3CertifiedScale n < 1 :=
    scaledMutationRate_lt_one hnpos hC_lt_n
  rw [wittMutationC3EnvelopeCondition_iff_closedForm
    (show 1 ≤ n by omega) hp1]
  by_cases hn9 : 9 ≤ n
  · have hn9R : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
    have hnreal_ne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
    have hCpos : 0 < wittMutationC3CertifiedScale := by
      norm_num [wittMutationC3CertifiedScale]
    have hdenpos : 0 < (n : ℝ) - wittMutationC3CertifiedScale := by
      exact sub_pos.mpr hC_lt_n
    have hden_ne : (n : ℝ) - wittMutationC3CertifiedScale ≠ 0 :=
      ne_of_gt hdenpos
    have hp_eq :
        scaledMutationRate wittMutationC3CertifiedScale n =
          wittMutationC3CertifiedScale / (n : ℝ) :=
      scaledMutationRate_eq_div_of_pos hnpos
    have hsurv_eq :
        1 - scaledMutationRate wittMutationC3CertifiedScale n =
          ((n : ℝ) - wittMutationC3CertifiedScale) / (n : ℝ) := by
      rw [hp_eq]
      field_simp [hnreal_ne]
    have hbase_eq :
        wittMutationBase (scaledMutationRate wittMutationC3CertifiedScale n) =
          (n : ℝ) / ((n : ℝ) - wittMutationC3CertifiedScale) := by
      unfold wittMutationBase
      rw [hsurv_eq, inv_div]
    have hbase_add :
        (n : ℝ) / ((n : ℝ) - wittMutationC3CertifiedScale) =
          1 + wittMutationC3CertifiedScale /
            ((n : ℝ) - wittMutationC3CertifiedScale) := by
      field_simp [hden_ne]
      ring
    have hz0 :
        0 ≤ wittMutationC3CertifiedScale /
          ((n : ℝ) - wittMutationC3CertifiedScale) :=
      div_nonneg hCpos.le hdenpos.le
    have hstep :
        1 + wittMutationC3CertifiedScale /
            ((n : ℝ) - wittMutationC3CertifiedScale) ≤
          Real.exp
            (wittMutationC3CertifiedScale /
              ((n : ℝ) - wittMutationC3CertifiedScale)) := by
      simpa [add_comm] using
        Real.add_one_le_exp
          (wittMutationC3CertifiedScale /
            ((n : ℝ) - wittMutationC3CertifiedScale))
    have hcastPred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      norm_num
    have hpow_exp :
        ((n : ℝ) / ((n : ℝ) - wittMutationC3CertifiedScale)) ^ (n - 1) ≤
          Real.exp
            (((n - 1 : ℕ) : ℝ) *
              (wittMutationC3CertifiedScale /
                ((n : ℝ) - wittMutationC3CertifiedScale))) := by
      rw [hbase_add]
      calc
        (1 + wittMutationC3CertifiedScale /
              ((n : ℝ) - wittMutationC3CertifiedScale)) ^ (n - 1) ≤
            (Real.exp
              (wittMutationC3CertifiedScale /
                ((n : ℝ) - wittMutationC3CertifiedScale))) ^ (n - 1) :=
          pow_le_pow_left₀ (by linarith : 0 ≤
            1 + wittMutationC3CertifiedScale /
              ((n : ℝ) - wittMutationC3CertifiedScale)) hstep (n - 1)
        _ = Real.exp
            (((n - 1 : ℕ) : ℝ) *
              (wittMutationC3CertifiedScale /
                ((n : ℝ) - wittMutationC3CertifiedScale))) := by
          exact
            (Real.exp_nat_mul
              (wittMutationC3CertifiedScale /
                ((n : ℝ) - wittMutationC3CertifiedScale)) (n - 1)).symm
    have harg :
        ((n - 1 : ℕ) : ℝ) *
            (wittMutationC3CertifiedScale /
              ((n : ℝ) - wittMutationC3CertifiedScale)) ≤
          (56 / 53 : ℝ) := by
      rw [hcastPred, ← mul_div_assoc]
      apply (div_le_iff₀ hdenpos).2
      norm_num [wittMutationC3CertifiedScale]
      nlinarith
    have hpow56 :
        ((n : ℝ) / ((n : ℝ) - wittMutationC3CertifiedScale)) ^ (n - 1) ≤
          Real.exp (56 / 53 : ℝ) :=
      hpow_exp.trans (Real.exp_le_exp.mpr harg)
    have he1 : Real.exp 1 ≤ (27183 / 10000 : ℝ) := by
      exact Real.exp_one_lt_d9.le.trans (by norm_num)
    have hesmall : Real.exp (3 / 53 : ℝ) ≤ (53 / 50 : ℝ) := by
      have h := Real.exp_bound_div_one_sub_of_interval
        (x := (3 / 53 : ℝ)) (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h
    have he56 :
        Real.exp (56 / 53 : ℝ) ≤
          (27183 / 10000 : ℝ) * (53 / 50 : ℝ) := by
      have hsplit : (56 / 53 : ℝ) = 1 + 3 / 53 := by norm_num
      rw [hsplit, Real.exp_add]
      calc
        Real.exp 1 * Real.exp (3 / 53 : ℝ) ≤
            (27183 / 10000 : ℝ) * Real.exp (3 / 53 : ℝ) :=
          mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
        _ ≤ (27183 / 10000 : ℝ) * (53 / 50 : ℝ) :=
          mul_le_mul_of_nonneg_left hesmall (by norm_num)
    have hp_le :
        scaledMutationRate wittMutationC3CertifiedScale n ≤ (7 / 60 : ℝ) := by
      rw [hp_eq]
      apply (div_le_iff₀ hnrealpos).2
      norm_num [wittMutationC3CertifiedScale]
      nlinarith
    have hsurv :
        (53 / 60 : ℝ) ≤
          1 - scaledMutationRate wittMutationC3CertifiedScale n := by
      linarith
    rw [hbase_eq]
    calc
      ((n : ℝ) / ((n : ℝ) - wittMutationC3CertifiedScale)) ^ (n - 1) -
          (1 - scaledMutationRate wittMutationC3CertifiedScale n) ≤
        ((27183 / 10000 : ℝ) * (53 / 50 : ℝ)) - (53 / 60 : ℝ) :=
          sub_le_sub (hpow56.trans he56) hsurv
      _ ≤ 2 := by norm_num
  · have hn8 : n ≤ 8 := by omega
    interval_cases n <;>
      norm_num [wittMutationC3CertifiedScale, scaledMutationRate, wittMutationBase]

/-- Every scale in `[0,21/20]` satisfies the exact finite C3 envelope from dimension four
onward. -/
theorem wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3CertifiedScale) :
    WittMutationC3EnvelopeCondition (scaledMutationRate c n) n := by
  have hnpos : 0 < n := by omega
  have hnreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hC_lt_n : wittMutationC3CertifiedScale < (n : ℝ) := by
    have hC4 : wittMutationC3CertifiedScale < (4 : ℝ) := by
      norm_num [wittMutationC3CertifiedScale]
    exact hC4.trans_le hnreal
  have hq1 : scaledMutationRate wittMutationC3CertifiedScale n < 1 :=
    scaledMutationRate_lt_one hnpos hC_lt_n
  have hpq :
      scaledMutationRate c n ≤
        scaledMutationRate wittMutationC3CertifiedScale n :=
    scaledMutationRate_mono_scale hnpos hc
  exact wittMutationC3EnvelopeCondition_mono
    (scaledMutationRate_nonneg hc0) hq1 hpq
    (wittMutationC3EnvelopeCondition_scaled_certifiedScale hn)

/-- C3 is nonnegative on the Stage-49 extended scaled interval. -/
theorem wittMutationCaseC3Contribution_nonneg_scaled_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    0 ≤ wittMutationCaseC3Contribution (scaledMutationRate c n) w x := by
  have hnpos : 0 < n := by omega
  have hnreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hC_lt_n : wittMutationC3CertifiedScale < (n : ℝ) := by
    have hC4 : wittMutationC3CertifiedScale < (4 : ℝ) := by
      norm_num [wittMutationC3CertifiedScale]
    exact hC4.trans_le hnreal
  have hq1 : scaledMutationRate wittMutationC3CertifiedScale n < 1 :=
    scaledMutationRate_lt_one hnpos hC_lt_n
  have hpq :
      scaledMutationRate c n ≤
        scaledMutationRate wittMutationC3CertifiedScale n :=
    scaledMutationRate_mono_scale hnpos hc
  have hp1 : scaledMutationRate c n < 1 := lt_of_le_of_lt hpq hq1
  exact wittMutationCaseC3Contribution_nonneg_of_envelope
    (scaledMutationRate_nonneg hc0) hp1 w hw hmono x
    (wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0 hc)

/-- The exact singleton-rate multiplicative drift theorem extends uniformly from
`c <= 1` to `c <= 21/20`. -/
theorem wittMutation_hasMultiplicativeDriftLowerBound_scaled_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
      (wittMutationLinearPotential (scaledMutationRate c n) w)
      (linearSingletonRate n (scaledMutationRate c n)) := by
  have hnpos : 0 < n := by omega
  have hnreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hC_lt_n : wittMutationC3CertifiedScale < (n : ℝ) := by
    have hC4 : wittMutationC3CertifiedScale < (4 : ℝ) := by
      norm_num [wittMutationC3CertifiedScale]
    exact hC4.trans_le hnreal
  have hq1 : scaledMutationRate wittMutationC3CertifiedScale n < 1 :=
    scaledMutationRate_lt_one hnpos hC_lt_n
  have hpq :
      scaledMutationRate c n ≤
        scaledMutationRate wittMutationC3CertifiedScale n :=
    scaledMutationRate_mono_scale hnpos hc
  have hp1 : scaledMutationRate c n < 1 := lt_of_le_of_lt hpq hq1
  exact wittMutation_hasMultiplicativeDriftLowerBound_of_c3Envelope
    (scaledMutationRate_nonneg hc0) hp1 w hw hmono
    (wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0 hc)

end ECRuntime
