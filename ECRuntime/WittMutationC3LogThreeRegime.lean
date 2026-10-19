import ECRuntime.WittMutationC3Envelope
import ECRuntime.WittMutationStrictTail
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 66: direct analytic C3 closure at `c = log 3`

The successive rational endpoint modules were useful while the proof architecture was being
identified, but their large finite `interval_cases` blocks do not scale to the natural boundary.
Stage 66 replaces that approach by a dimension-uniform logarithmic argument.

For `L = log 3` and `x = L/n`, the closed C3 condition is

`(1-x)^(-(n-1)) <= 3-x`.

The proof compares logarithms.  The left side uses the first nontrivial explicit remainder
bound for the atanh/logarithm series,

`-log(1-x) <= x + x^2/(2(1-x))`,

obtained from `Real.log_div_le_sum_range_add` after the substitution `y=x/(2-x)`.  The
right side uses `Real.one_sub_inv_le_log_of_pos` to obtain

`log(3-x) >= log 3 - x/(3-x)`.

The remaining inequality is rational in `L` and `n`.  Coarse certified bounds
`1 < log 3 < 7/6` suffice; at the upper endpoint its numerator factors as
`(2n-7)(9n-7)/36`, hence is nonnegative for every `n >= 4`.

The Stage 66 fix-6 verification run compiled this module and the complete root build warning/error-free, promoting the exact finite boundary.
-/

/-- Natural limiting scale of the finite C3 argument. -/
noncomputable def wittMutationC3LogThreeScale : ℝ := Real.log 3

@[simp] theorem wittMutationC3LogThreeScale_eq :
    wittMutationC3LogThreeScale = Real.log 3 := by
  rfl

private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
  exact Real.exp_one_lt_d9.trans (by norm_num)

private theorem log_three_lt_seven_sixths : Real.log 3 < (7 / 6 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2
  have hsmall : (7 / 6 : ℝ) ≤ Real.exp (1 / 6 : ℝ) := by
    convert Real.add_one_le_exp (1 / 6 : ℝ) using 1
    all_goals norm_num
  calc
    (3 : ℝ) < (2.7182818283 : ℝ) * (7 / 6 : ℝ) := by norm_num
    _ < Real.exp 1 * (7 / 6 : ℝ) :=
      mul_lt_mul_of_pos_right Real.exp_one_gt_d9 (by norm_num)
    _ ≤ Real.exp 1 * Real.exp (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos 1).le
    _ = Real.exp (7 / 6 : ℝ) := by
      rw [← Real.exp_add]
      congr 1
      norm_num

/-- Explicit second-order upper bound on `-log(1-x)` for `0 <= x < 1`. -/
private theorem neg_log_one_sub_le_quadratic
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / (2 * (1 - x)) := by
  let y : ℝ := x / (2 - x)
  have h2x : 0 < 2 - x := by linarith
  have h2xne : 2 - x ≠ 0 := ne_of_gt h2x
  have h1x : 0 < 1 - x := sub_pos.mpr hx1
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg hx0 h2x.le
  have hy1 : y < 1 := by
    dsimp [y]
    exact (div_lt_one h2x).2 (by linarith)
  have hyden : 0 < 1 - y ^ 2 := by
    have hid : 1 - y ^ 2 = 4 * (1 - x) / (2 - x) ^ 2 := by
      dsimp [y]
      field_simp [h2xne]
      ring
    rw [hid]
    positivity
  have htwo : 0 < 2 - x * 2 := by nlinarith
  have hfour : 0 < 4 - x * 4 := by nlinarith
  have hseries := Real.log_div_le_sum_range_add hy0 hy1 1
  have hseries' :
      (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)) ≤
        y + y ^ 3 / (1 - y ^ 2) := by
    simpa [Finset.sum_range_succ] using hseries
  have hratio : (1 + y) / (1 - y) = (1 - x)⁻¹ := by
    dsimp [y]
    field_simp [h2xne, h1x.ne', (ne_of_gt htwo)]
    have hcancel :
        (2 - x * 2)⁻¹ * (2 - x * 2) = (1 : ℝ) :=
      inv_mul_cancel₀ (ne_of_gt htwo)
    ring_nf at hcancel ⊢
    exact hcancel
  have hrhs :
      2 * (y + y ^ 3 / (1 - y ^ 2)) =
        x + x ^ 2 / (2 * (1 - x)) := by
    dsimp [y]
    field_simp [h2xne, h1x.ne', hyden.ne', (ne_of_gt htwo), (ne_of_gt hfour)]
    have hcancel :
        (4 - x * 4)⁻¹ * (4 - x * 4) = (1 : ℝ) :=
      inv_mul_cancel₀ (ne_of_gt hfour)
    have hcancelScaled :
        x ^ 3 * ((4 - x * 4)⁻¹ * (4 - x * 4)) = x ^ 3 := by
      calc
        x ^ 3 * ((4 - x * 4)⁻¹ * (4 - x * 4)) = x ^ 3 * 1 :=
          congrArg (fun z : ℝ => x ^ 3 * z) hcancel
        _ = x ^ 3 := mul_one _
    ring_nf at hcancelScaled ⊢
    linarith only [hcancelScaled]
  have hscaled :
      Real.log ((1 + y) / (1 - y)) ≤
        2 * (y + y ^ 3 / (1 - y ^ 2)) := by
    linarith
  rw [hratio, Real.log_inv, hrhs] at hscaled
  exact hscaled

/-- Elementary lower bound on `log(3-x)` used by the boundary proof. -/
private theorem log_three_sub_lower
    {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log 3 - x / (3 - x) ≤ Real.log (3 - x) := by
  have hsmall : 0 < 1 - x / 3 := by nlinarith
  have hsmallne : 1 - x / 3 ≠ 0 := ne_of_gt hsmall
  have h3x : 0 < 3 - x := by linarith
  have h3xne : 3 - x ≠ 0 := ne_of_gt h3x
  have hbasic := Real.one_sub_inv_le_log_of_pos hsmall
  have hid : 1 - (1 - x / 3)⁻¹ = -(x / (3 - x)) := by
    field_simp [hsmallne, h3xne]
    ring
  rw [hid] at hbasic
  have hprod : (3 : ℝ) - x = 3 * (1 - x / 3) := by ring
  calc
    Real.log 3 - x / (3 - x) = Real.log 3 + (-(x / (3 - x))) := by ring
    _ ≤ Real.log 3 + Real.log (1 - x / 3) := by
      linarith
    _ = Real.log (3 - x) := by
      rw [hprod, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hsmallne]

/-- The rational comparison left after the two logarithmic estimates. -/
private theorem log_three_rational_balance
    {n : ℕ} (hn : 4 ≤ n) :
    let L : ℝ := Real.log 3
    let x : ℝ := L / (n : ℝ)
    ((n - 1 : ℕ) : ℝ) * (x + x ^ 2 / (2 * (1 - x))) ≤
      L - x / (3 - x) := by
  dsimp
  let L : ℝ := Real.log 3
  have hL1 : (1 : ℝ) < L := by simpa [L] using one_lt_log_three
  have hLU : L < (7 / 6 : ℝ) := by simpa [L] using log_three_lt_seven_sixths
  have hL0 : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL1.le
  have hnR4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : 0 < (n : ℝ) := by positivity
  have hcastPred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    norm_num
  have hnL : 0 < (n : ℝ) - L := by nlinarith
  have h3nL : 0 < 3 * (n : ℝ) - L := by nlinarith
  let P : ℝ :=
    L ^ 2 * (n : ℝ) + L ^ 2 - 3 * L * (n : ℝ) ^ 2 -
      3 * L * (n : ℝ) + 4 * (n : ℝ) ^ 2
  have hdiff0 :
      0 ≤ ((7 / 6 : ℝ) - L) * ((n : ℝ) + 1) *
        (3 * (n : ℝ) - L - 7 / 6) := by
    have h1 : 0 ≤ (7 / 6 : ℝ) - L := by linarith
    have h2 : 0 ≤ (n : ℝ) + 1 := by positivity
    have h3 : 0 ≤ 3 * (n : ℝ) - L - 7 / 6 := by nlinarith
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hPupper :
      0 ≤
        ((7 / 6 : ℝ) ^ 2 * (n : ℝ) + (7 / 6 : ℝ) ^ 2 -
          3 * (7 / 6 : ℝ) * (n : ℝ) ^ 2 -
          3 * (7 / 6 : ℝ) * (n : ℝ) + 4 * (n : ℝ) ^ 2) := by
    have h1 : 0 ≤ 2 * (n : ℝ) - 7 := by nlinarith
    have h2 : 0 ≤ 9 * (n : ℝ) - 7 := by nlinarith
    have hp := mul_nonneg h1 h2
    nlinarith
  have hP : 0 ≤ P := by
    have hid :
        P =
          ((7 / 6 : ℝ) ^ 2 * (n : ℝ) + (7 / 6 : ℝ) ^ 2 -
            3 * (7 / 6 : ℝ) * (n : ℝ) ^ 2 -
            3 * (7 / 6 : ℝ) * (n : ℝ) + 4 * (n : ℝ) ^ 2) +
          ((7 / 6 : ℝ) - L) * ((n : ℝ) + 1) *
            (3 * (n : ℝ) - L - 7 / 6) := by
      dsimp [P]
      ring
    rw [hid]
    exact add_nonneg hPupper hdiff0
  have hden : 0 < 2 * (n : ℝ) * ((n : ℝ) - L) * (3 * (n : ℝ) - L) := by
    positivity
  have hfrac :
      0 ≤ L * P /
        (2 * (n : ℝ) * ((n : ℝ) - L) * (3 * (n : ℝ) - L)) :=
    div_nonneg (mul_nonneg hL0 hP) hden.le
  have hone :
      1 - L / (n : ℝ) = ((n : ℝ) - L) / (n : ℝ) := by
    field_simp [ne_of_gt hnRpos]
  have hthree :
      3 - L / (n : ℝ) = (3 * (n : ℝ) - L) / (n : ℝ) := by
    field_simp [ne_of_gt hnRpos]
  have h3nL' : 0 < (n : ℝ) * 3 - L := by nlinarith
  have hid :
      (L - (L / (n : ℝ)) / (3 - L / (n : ℝ))) -
          (((n - 1 : ℕ) : ℝ) *
            ((L / (n : ℝ)) + (L / (n : ℝ)) ^ 2 /
              (2 * (1 - L / (n : ℝ))))) =
        L * P /
          (2 * (n : ℝ) * ((n : ℝ) - L) * (3 * (n : ℝ) - L)) := by
    rw [hcastPred, hone, hthree]
    dsimp [P]
    field_simp [ne_of_gt hnRpos, ne_of_gt hnL, ne_of_gt h3nL, ne_of_gt h3nL']
    ring
  rw [← sub_nonneg, hid]
  exact hfrac

/-- At the natural boundary `c = log 3`, the exact finite C3 envelope holds for every
`n >= 4`.  This is the Stage-66 promoted boundary theorem. -/
theorem wittMutationC3EnvelopeCondition_scaled_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) :
    WittMutationC3EnvelopeCondition
      (scaledMutationRate wittMutationC3LogThreeScale n) n := by
  have hnpos : 0 < n := by omega
  let L : ℝ := Real.log 3
  let x : ℝ := L / (n : ℝ)
  have hL1 : (1 : ℝ) < L := by simpa [L] using one_lt_log_three
  have hLU : L < (7 / 6 : ℝ) := by simpa [L] using log_three_lt_seven_sixths
  have hL0 : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL1.le
  have hnR4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : 0 < (n : ℝ) := by positivity
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg hL0 hnRpos.le
  have hx1 : x < 1 := by
    dsimp [x]
    apply (div_lt_one hnRpos).2
    nlinarith
  have hp_eq :
      scaledMutationRate wittMutationC3LogThreeScale n = x := by
    rw [scaledMutationRate_eq_div_of_pos hnpos]
    rfl
  have hp1 : scaledMutationRate wittMutationC3LogThreeScale n < 1 := by
    rw [hp_eq]
    exact hx1
  rw [wittMutationC3EnvelopeCondition_iff_closedForm
    (show 1 ≤ n by omega) hp1]
  rw [hp_eq]
  have hneglog := neg_log_one_sub_le_quadratic hx0 hx1
  have hbalance := log_three_rational_balance hn
  have hright := log_three_sub_lower hx0 hx1
  have hlog :
      ((n - 1 : ℕ) : ℝ) * (-Real.log (1 - x)) ≤ Real.log (3 - x) := by
    exact (mul_le_mul_of_nonneg_left hneglog (Nat.cast_nonneg (n - 1))).trans
      (hbalance.trans hright)
  have hbasepos : 0 < wittMutationBase x := wittMutationBase_pos hx1
  have hpowpos : 0 < wittMutationBase x ^ (n - 1) := pow_pos hbasepos _
  have hrhspos : 0 < 3 - x := by linarith
  have hlogpow :
      Real.log (wittMutationBase x ^ (n - 1)) ≤ Real.log (3 - x) := by
    rw [Real.log_pow]
    unfold wittMutationBase
    rw [Real.log_inv]
    exact hlog
  have hexp :
      Real.exp (Real.log (wittMutationBase x ^ (n - 1))) ≤
        Real.exp (Real.log (3 - x)) :=
    (Real.exp_le_exp).2 hlogpow
  rw [Real.exp_log hpowpos, Real.exp_log hrhspos] at hexp
  linarith

/-- Every scale `0 <= c <= log 3` satisfies the exact finite C3 envelope from dimension four. -/
theorem wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3LogThreeScale) :
    WittMutationC3EnvelopeCondition (scaledMutationRate c n) n := by
  have hnpos : 0 < n := by omega
  have hL_lt_n : wittMutationC3LogThreeScale < (n : ℝ) := by
    have hL4 : wittMutationC3LogThreeScale < (4 : ℝ) := by
      rw [wittMutationC3LogThreeScale_eq]
      exact log_three_lt_seven_sixths.trans (by norm_num)
    exact hL4.trans_le (by exact_mod_cast hn)
  exact wittMutationC3EnvelopeCondition_scaled_of_endpoint
    hnpos hc0 hc hL_lt_n
    (wittMutationC3EnvelopeCondition_scaled_logThreeScale hn)

/-- Every scaled mutation rate on the log-three interval is strictly below one in dimension at least four. -/
theorem scaledMutationRate_lt_one_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc : c ≤ wittMutationC3LogThreeScale) :
    scaledMutationRate c n < 1 := by
  have hnpos : 0 < n := by omega
  have hL_lt_n : wittMutationC3LogThreeScale < (n : ℝ) := by
    rw [wittMutationC3LogThreeScale_eq]
    have hL4 : Real.log 3 < (4 : ℝ) :=
      log_three_lt_seven_sixths.trans (by norm_num)
    exact hL4.trans_le (by exact_mod_cast hn)
  exact lt_of_le_of_lt (scaledMutationRate_mono_scale hnpos hc)
    (scaledMutationRate_lt_one hnpos hL_lt_n)

/-- C3 is nonnegative throughout the promoted interval `0 <= c <= log 3`. -/
theorem wittMutationCaseC3Contribution_nonneg_scaled_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    0 ≤ wittMutationCaseC3Contribution (scaledMutationRate c n) w x := by
  have hnpos : 0 < n := by omega
  have hL_lt_n : wittMutationC3LogThreeScale < (n : ℝ) := by
    rw [wittMutationC3LogThreeScale_eq]
    have hL4 : Real.log 3 < (4 : ℝ) :=
      log_three_lt_seven_sixths.trans (by norm_num)
    exact hL4.trans_le (by exact_mod_cast hn)
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt (scaledMutationRate_mono_scale hnpos hc)
      (scaledMutationRate_lt_one hnpos hL_lt_n)
  exact wittMutationCaseC3Contribution_nonneg_of_envelope
    (scaledMutationRate_nonneg hc0) hp1 w hw hmono x
    (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0 hc)

/-- Exact-singleton-rate multiplicative drift theorem on the full natural C3 interval. -/
theorem wittMutation_hasMultiplicativeDriftLowerBound_scaled_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
      (wittMutationLinearPotential (scaledMutationRate c n) w)
      (linearSingletonRate n (scaledMutationRate c n)) := by
  have hnpos : 0 < n := by omega
  have hL_lt_n : wittMutationC3LogThreeScale < (n : ℝ) := by
    rw [wittMutationC3LogThreeScale_eq]
    have hL4 : Real.log 3 < (4 : ℝ) :=
      log_three_lt_seven_sixths.trans (by norm_num)
    exact hL4.trans_le (by exact_mod_cast hn)
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt (scaledMutationRate_mono_scale hnpos hc)
      (scaledMutationRate_lt_one hnpos hL_lt_n)
  exact wittMutation_hasMultiplicativeDriftLowerBound_of_c3Envelope
    (scaledMutationRate_nonneg hc0) hp1 w hw hmono
    (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0 hc)

end ECRuntime
