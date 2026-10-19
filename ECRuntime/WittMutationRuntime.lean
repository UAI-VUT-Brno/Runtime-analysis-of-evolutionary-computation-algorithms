import ECRuntime.WittMutationRateAsymptotics
import ECRuntime.AsymptoticRegime
import Mathlib

open scoped BigOperators ENNReal
open Filter
open Asymptotics

namespace ECRuntime

/-!
# Stage 47: fixed-scale Witt runtime endpoint

Stage 46 identifies the normalized exact singleton drift rate in the scaled regime
`p = c/n` and proves that its inverse leading factor converges to `exp(c)/c`, with the
factor minimized at `c = 1`.  This module attaches that constant to the finite runtime
layer on the currently compiler-verified regime `0 < c <= 1`, `n >= 4`.

The key finite estimate is stronger than a bare limit statement.  Writing `m = n-1`,

`(linearSingletonRate n (c/n))⁻¹ <= (exp(c)/c) * n`.

Indeed,

`n/(n-c) <= 1 + c/(n-1)`

for `0 <= c <= 1`, and `(1 + c/(n-1))^(n-1) <= exp(c)`.  Together with the
parameterized Witt-potential envelope `V <= e n`, the generic multiplicative-drift
runtime theorem yields

`runtime <= (exp(c)/c) * n * (2 + log n)`.

This envelope splits exactly into

`(exp(c)/c) * n log n + 2 (exp(c)/c) * n`,

and the second term is formally `O(n)`.  Thus Stage 47 exposes the complete fixed-scale
upper-bound constant without reopening the C2/C3 proof.
-/

/-- On the verified scaled interval, the parameterized Witt potential is still bounded
by the promoted standard-rate envelope `e n`. -/
theorem wittMutationLinearPotential_scaled_le_en
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential (scaledMutationRate c n) w x ≤
      Real.exp 1 * (n : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hp0 : 0 ≤ scaledMutationRate c n := scaledMutationRate_nonneg hc0
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0 hc1
  have hstdlt : standardMutationRate n < 1 := standardMutationRate_lt_one hn2
  have hp1 : scaledMutationRate c n < 1 := lt_of_le_of_lt hp_le hstdlt
  have hbase := wittMutationBase_scaled_le_standard hn hc0 hc1
  have hpow :
      wittMutationBase (scaledMutationRate c n) ^ (n - 1) ≤
        wittStandardBase n ^ (n - 1) :=
    pow_le_pow_left₀ (wittMutationBase_pos hp1).le hbase (n - 1)
  have hpowexp :
      wittMutationBase (scaledMutationRate c n) ^ (n - 1) ≤ Real.exp 1 :=
    hpow.trans (wittStandardBase_fullPower_le_exp_one n)
  have hV := wittMutationLinearPotential_le_n_mul_fullPower hp0 hp1 w x
  calc
    wittMutationLinearPotential (scaledMutationRate c n) w x ≤
        (n : ℝ) * wittMutationBase (scaledMutationRate c n) ^ (n - 1) := hV
    _ ≤ (n : ℝ) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hpowexp (Nat.cast_nonneg n)
    _ = Real.exp 1 * (n : ℝ) := by ring

/-- The zero level of the scaled parameterized Witt potential is the canonical all-ones
target. -/
theorem wittMutationLinearTarget_eq_oneMaxTarget_scaled
    {n : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hp1 : scaledMutationRate c n < 1)
    (w : Fin n → ℝ) :
    realPotentialTarget
        (wittMutationLinearPotential (scaledMutationRate c n) w) =
      oneMaxTarget n := by
  rw [oneMaxTarget_eq_singleton]
  ext x
  simpa [realPotentialTarget] using
    (wittMutationLinearPotential_eq_zero_iff
      (scaledMutationRate_nonneg hc0) hp1 w x)

/-- The Stage-45 drift theorem plugged into the generic multiplicative-drift runtime
certificate at the scaled mutation rate. -/
theorem wittMutation_runtimeSup_le_certificate_scaled_of_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          (scaledLinearSingletonRate c n) 1
          (wittMutationLinearPotential (scaledMutationRate c n) w) x) := by
  have hnpos : 0 < n := by omega
  have hp0 : 0 < scaledMutationRate c n :=
    scaledMutationRate_pos hc0 hnpos
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0.le hc1
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt hp_le (standardMutationRate_lt_one (by omega : 2 ≤ n))
  have hP : IsStochastic
      (onePlusOneTransition (scaledMutationRate c n) (linearFitness w)) :=
    onePlusOneTransition_stochastic hp0.le hp1.le (linearFitness w)
  have hratePos : 0 < scaledLinearSingletonRate c n := by
    simpa [scaledLinearSingletonRate] using (linearSingletonRate_pos hp0 hp1)
  have hmult :
      HasMultiplicativeDriftLowerBound
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (wittMutationLinearPotential (scaledMutationRate c n) w)
        (scaledLinearSingletonRate c n) := by
    simpa [scaledLinearSingletonRate] using
      (wittMutation_hasMultiplicativeDriftLowerBound_scaled_of_le_one
        hn hc0.le hc1 w hw hmono)
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget
          (wittMutationLinearPotential (scaledMutationRate c n) w) →
        (1 : ℝ) ≤ wittMutationLinearPotential (scaledMutationRate c n) w z := by
    intro z hz
    apply one_le_wittMutationLinearPotential_of_ne_allOnes hp0.le hp1 w z
    intro hall
    apply hz
    change wittMutationLinearPotential (scaledMutationRate c n) w z = 0
    rw [hall]
    exact wittMutationLinearPotential_allOnes (scaledMutationRate c n) w
  have hbound := multiplicativeDrift_runtimeSup_le
    (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
    (wittMutationLinearPotential (scaledMutationRate c n) w)
    (scaledLinearSingletonRate c n) 1
    hP hratePos (by norm_num)
    (wittMutationLinearPotential_nonneg hp0.le hp1 w) hmin hmult x
  calc
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x =
      runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (realPotentialTarget
          (wittMutationLinearPotential (scaledMutationRate c n) w)) x := by
          symm
          exact runtimeSup_congr_target
            (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
            (realPotentialTarget
              (wittMutationLinearPotential (scaledMutationRate c n) w))
            (oneMaxTarget n)
            (wittMutationLinearTarget_eq_oneMaxTarget_scaled hc0.le hp1 w) x
    _ ≤ ENNReal.ofReal
        (multiplicativeDriftRuntime
          (scaledLinearSingletonRate c n) 1
          (wittMutationLinearPotential (scaledMutationRate c n) w) x) := hbound

/-- The exact multiplicative-drift certificate is bounded by the inverse singleton rate
times `2 + log n`. -/
theorem wittMutation_multiplicativeRuntime_le_inverseRate_log_bound
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) :
    multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1
        (wittMutationLinearPotential (scaledMutationRate c n) w) x ≤
      (scaledLinearSingletonRate c n)⁻¹ * (2 + Real.log (n : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnrealne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  have hp0 : 0 < scaledMutationRate c n :=
    scaledMutationRate_pos hc0 hnpos
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0.le hc1
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt hp_le (standardMutationRate_lt_one (by omega : 2 ≤ n))
  have hratePos : 0 < scaledLinearSingletonRate c n := by
    simpa [scaledLinearSingletonRate] using (linearSingletonRate_pos hp0 hp1)
  let V := wittMutationLinearPotential (scaledMutationRate c n) w
  let C : ℝ := Real.exp 1 * (n : ℝ)
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.exp_pos 1) hnrealpos
  have hlogC : Real.log C = 1 + Real.log (n : ℝ) := by
    dsimp [C]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) hnrealne]
    simp
  change multiplicativeDriftRuntime
      (scaledLinearSingletonRate c n) 1 V x ≤
    (scaledLinearSingletonRate c n)⁻¹ * (2 + Real.log (n : ℝ))
  by_cases hx0 : V x = 0
  · have hcert : multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1 V x = 0 := by
      unfold multiplicativeDriftRuntime additiveDriftRuntime
      simp [multiplicativeDriftPotential, hx0]
    rw [hcert]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
    exact mul_nonneg (inv_nonneg.mpr hratePos.le) (by linarith)
  · have hxpos : 0 < V x := by
      have hnonneg : 0 ≤ V x := by
        dsimp [V]
        exact wittMutationLinearPotential_nonneg hp0.le hp1 w x
      exact lt_of_le_of_ne hnonneg (Ne.symm hx0)
    have hVupper : V x ≤ C := by
      dsimp [V, C]
      exact wittMutationLinearPotential_scaled_le_en hn hc0.le hc1 w x
    have hlog : Real.log (V x) ≤ Real.log C :=
      Real.log_le_log hxpos hVupper
    have hcert : multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1 V x =
          (scaledLinearSingletonRate c n)⁻¹ * (1 + Real.log (V x)) := by
      have hraw := multiplicativeDriftRuntime_eq_log_ratio
        V (scaledLinearSingletonRate c n) 1 (by norm_num) x hx0
      simpa only [div_one] using hraw
    rw [hcert]
    rw [hlogC] at hlog
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hratePos.le)

/-- For `0 < c <= 1`, the exact inverse singleton rate is bounded pointwise by its
asymptotic leading coefficient times `n`. -/
theorem scaledLinearSingletonRate_inv_le_leadingFactor_mul_n
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (scaledLinearSingletonRate c n)⁻¹ ≤
      wittMutationLeadingRuntimeFactor c * (n : ℝ) := by
  let m : ℕ := n - 1
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hm_succ : m + 1 = n := by
    dsimp [m]
    omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmrealpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hnreal_ne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  have hmreal_ne : (m : ℝ) ≠ 0 := ne_of_gt hmrealpos
  have hncpos : 0 < (n : ℝ) - c := by
    have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hmcast : (m : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hm_succ
  have hp : scaledMutationRate c n = c / (n : ℝ) :=
    scaledMutationRate_eq_div_of_pos hnpos
  have hbase :
      1 - c / (n : ℝ) = ((n : ℝ) - c) / (n : ℝ) := by
    field_simp [hnreal_ne]
  have hratio :
      (n : ℝ) / ((n : ℝ) - c) ≤ 1 + c / (m : ℝ) := by
    apply (div_le_iff₀ hncpos).2
    have hid :
        (1 + c / (m : ℝ)) * ((n : ℝ) - c) =
          (n : ℝ) + c * (1 - c) / (m : ℝ) := by
      rw [← hmcast]
      field_simp [hmreal_ne]
      ring
    rw [hid]
    have hcorr : 0 ≤ c * (1 - c) / (m : ℝ) :=
      div_nonneg (mul_nonneg hc0.le (sub_nonneg.mpr hc1)) hmrealpos.le
    linarith
  have hratio0 : 0 ≤ (n : ℝ) / ((n : ℝ) - c) :=
    div_nonneg hnrealpos.le hncpos.le
  have hpowRatio :
      ((n : ℝ) / ((n : ℝ) - c)) ^ m ≤
        (1 + c / (m : ℝ)) ^ m :=
    pow_le_pow_left₀ hratio0 hratio m
  have hstep :
      1 + c / (m : ℝ) ≤ Real.exp (c / (m : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (c / (m : ℝ))
  have hleft0 : 0 ≤ 1 + c / (m : ℝ) := by
    have hfrac : 0 ≤ c / (m : ℝ) := div_nonneg hc0.le hmrealpos.le
    linarith
  have hpowExp :
      (1 + c / (m : ℝ)) ^ m ≤ Real.exp c := by
    calc
      (1 + c / (m : ℝ)) ^ m ≤
          (Real.exp (c / (m : ℝ))) ^ m :=
        pow_le_pow_left₀ hleft0 hstep m
      _ = Real.exp c := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp [hmreal_ne]
  have hrate :
      (scaledLinearSingletonRate c n)⁻¹ =
        ((n : ℝ) / c) *
          (((n : ℝ) / ((n : ℝ) - c)) ^ m) := by
    unfold scaledLinearSingletonRate linearSingletonRate
    rw [hp, show n - 1 = m by rfl, hbase]
    rw [mul_inv_rev, ← inv_pow]
    simp only [inv_div]
    ring
  rw [hrate]
  have hpref0 : 0 ≤ (n : ℝ) / c :=
    div_nonneg hnrealpos.le hc0.le
  calc
    ((n : ℝ) / c) * (((n : ℝ) / ((n : ℝ) - c)) ^ m) ≤
        ((n : ℝ) / c) * (1 + c / (m : ℝ)) ^ m :=
      mul_le_mul_of_nonneg_left hpowRatio hpref0
    _ ≤ ((n : ℝ) / c) * Real.exp c :=
      mul_le_mul_of_nonneg_left hpowExp hpref0
    _ = wittMutationLeadingRuntimeFactor c * (n : ℝ) := by
      unfold wittMutationLeadingRuntimeFactor
      ring

/-- Coefficient-independent finite-dimensional runtime bound on the verified fixed-scale
regime. -/
theorem wittMutation_runtimeSup_le_scaled_log_bound
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        ((wittMutationLeadingRuntimeFactor c * (n : ℝ)) *
          (2 + Real.log (n : ℝ))) := by
  have hcert := wittMutation_runtimeSup_le_certificate_scaled_of_le_one
    hn hc0 hc1 w hw hmono x
  have hmult := wittMutation_multiplicativeRuntime_le_inverseRate_log_bound
    hn hc0 hc1 w x
  have hrate := scaledLinearSingletonRate_inv_le_leadingFactor_mul_n
    hn hc0 hc1
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hfac : 0 ≤ 2 + Real.log (n : ℝ) := by linarith
  have hfinite :
      multiplicativeDriftRuntime
          (scaledLinearSingletonRate c n) 1
          (wittMutationLinearPotential (scaledMutationRate c n) w) x ≤
        (wittMutationLeadingRuntimeFactor c * (n : ℝ)) *
          (2 + Real.log (n : ℝ)) :=
    hmult.trans (mul_le_mul_of_nonneg_right hrate hfac)
  exact hcert.trans (ENNReal.ofReal_le_ofReal hfinite)

/-- Leading `(exp(c)/c) n log n` term for the Stage-47 fixed-scale runtime bound. -/
noncomputable def wittMutationScaledRuntimeLeadingTerm (c : ℝ) (n : ℕ) : ℝ :=
  wittMutationLeadingRuntimeFactor c * natLinearLogGrowth n

/-- Linear correction in the Stage-47 fixed-scale runtime bound. -/
noncomputable def wittMutationScaledRuntimeLinearCorrection (c : ℝ) (n : ℕ) : ℝ :=
  (2 * wittMutationLeadingRuntimeFactor c) * natLinearGrowth n

/-- Explicit finite-dimensional Stage-47 upper envelope. -/
noncomputable def wittMutationScaledRuntimeUpperBound (c : ℝ) (n : ℕ) : ℝ :=
  (wittMutationLeadingRuntimeFactor c * (n : ℝ)) *
    (2 + Real.log (n : ℝ))

/-- The finite scaled-rate runtime envelope splits exactly into its leading term and a
linear correction. -/
theorem wittMutationScaledRuntimeUpperBound_eq_leading_add_linear
    (c : ℝ) (n : ℕ) :
    wittMutationScaledRuntimeUpperBound c n =
      wittMutationScaledRuntimeLeadingTerm c n +
        wittMutationScaledRuntimeLinearCorrection c n := by
  unfold wittMutationScaledRuntimeUpperBound
    wittMutationScaledRuntimeLeadingTerm
    wittMutationScaledRuntimeLinearCorrection
    natLinearLogGrowth natLinearGrowth
  ring

/-- For every fixed positive scale, the Stage-47 correction is `O(n)`. -/
theorem wittMutationScaledRuntimeLinearCorrection_isBigO
    (c : ℝ) :
    NatIsBigO (wittMutationScaledRuntimeLinearCorrection c) natLinearGrowth := by
  unfold wittMutationScaledRuntimeLinearCorrection
  exact Asymptotics.isBigO_const_mul_self
    (2 * wittMutationLeadingRuntimeFactor c) natLinearGrowth Filter.atTop

/-- Formal `(exp(c)/c) n log n + O(n)` decomposition of the finite upper envelope. -/
theorem wittMutationScaledRuntimeUpperBound_eq_leading_add_bigO_n
    (c : ℝ) :
    ∃ r : ℕ → ℝ,
      NatIsBigO r natLinearGrowth ∧
      ∀ n : ℕ,
        wittMutationScaledRuntimeUpperBound c n =
          wittMutationScaledRuntimeLeadingTerm c n + r n := by
  refine ⟨wittMutationScaledRuntimeLinearCorrection c,
    wittMutationScaledRuntimeLinearCorrection_isBigO c, ?_⟩
  intro n
  exact wittMutationScaledRuntimeUpperBound_eq_leading_add_linear c n

/-- Runtime theorem restated through the named Stage-47 asymptotic upper envelope. -/
theorem wittMutation_runtimeSup_le_scaled_asymptotic_upperBound
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (wittMutationScaledRuntimeUpperBound c n) := by
  unfold wittMutationScaledRuntimeUpperBound
  exact wittMutation_runtimeSup_le_scaled_log_bound hn hc0 hc1 w hw hmono x

/-- Equivalent explicit form of the Stage-47 result: the runtime is bounded by the
leading fixed-scale term plus a linear correction. -/
theorem wittMutation_runtimeSup_le_scaled_leading_add_linear
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (wittMutationScaledRuntimeLeadingTerm c n +
          wittMutationScaledRuntimeLinearCorrection c n) := by
  rw [← wittMutationScaledRuntimeUpperBound_eq_leading_add_linear c n]
  exact wittMutation_runtimeSup_le_scaled_asymptotic_upperBound
    hn hc0 hc1 w hw hmono x

end ECRuntime
