import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.AsymptoticRegime
import Mathlib

open Filter

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 87: asymptotically sharp upper envelope with bounded factorial moments

The explicit Stage-85 bound permits an arbitrary calibration `alpha > 1`.
Instead of fixing it to two, take `alpha(n) = 2 + sqrt(log n)`.  Its inverse
vanishes, while its ratio to `log n` vanishes.  This gives a leading upper
coefficient of `1/p₁` for mutation-law families with a *uniform bound* on
`chi * E[K(K-1)] / p₁²`.

The limit below is of the explicit upper envelope, NOT of the expected runtime
itself.  In particular, no corresponding lower bound and no bounded-mean-only
version of the Doerr--Janett--Lengler theorem is claimed here.

This candidate is deliberately outside the promoted root until it passes
focused verification, theorem/axiom evidence, and later integration checks.
-/

/-- A calibration that grows, but is negligible compared with `log n`. -/
noncomputable def correctedMomentSlack (n : ℕ) : ℝ :=
  2 + Real.sqrt (Real.log (n : ℝ))

/-- Reciprocal square-root logarithm used in the sharp-envelope calculation. -/
noncomputable def correctedMomentReciprocalSqrtLog (n : ℕ) : ℝ :=
  (Real.sqrt (Real.log (n : ℝ)))⁻¹

/-- The normalized Stage-85 logarithmic factor, with a fixed moment-ratio
upper bound `D` in place of the mutation-law-dependent second moment. -/
noncomputable def correctedNormalizedMomentEnvelope (D : ℝ) (n : ℕ) : ℝ :=
  (1 + Real.log (n : ℝ) + correctedMomentSlack n * D) /
    ((1 - 1 / correctedMomentSlack n) * Real.log (n : ℝ))

/-- A rational expression in `t = (sqrt (log n))⁻¹`.  It is continuous at
`t = 0`, where its value is exactly one. -/
noncomputable def correctedNormalizedMomentRational (D t : ℝ) : ℝ :=
  ((1 + D * t + (1 + 2 * D) * t ^ 2) * (1 + 2 * t)) / (1 + t)

/-- The dimension-dependent calibration is strictly larger than one. -/
theorem one_lt_correctedMomentSlack (n : ℕ) :
    1 < correctedMomentSlack n := by
  unfold correctedMomentSlack
  have hs := Real.sqrt_nonneg (Real.log (n : ℝ))
  linarith

/-- Both asymptotic properties of the calibrated slack, proved from the
standard `log` and `sqrt` limits.  The second component is the critical
`alpha(n) = o(log n)` assertion. -/
theorem correctedMomentSlack_growth :
    Filter.Tendsto correctedMomentSlack Filter.atTop Filter.atTop ∧
    Filter.Tendsto
      (fun n : ℕ => correctedMomentSlack n / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto
      (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hslack : Filter.Tendsto correctedMomentSlack
      Filter.atTop Filter.atTop := by
    apply tendsto_atTop_mono' Filter.atTop
      (Filter.Eventually.of_forall (fun n : ℕ => by
        unfold correctedMomentSlack
        linarith)) hs
  have hslackInv : Filter.Tendsto correctedMomentReciprocalSqrtLog
      Filter.atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hs
  have hlogInv : Filter.Tendsto
      (fun n : ℕ => (Real.log (n : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hsum : Filter.Tendsto
      (fun n : ℕ =>
        2 * (Real.log (n : ℝ))⁻¹ + correctedMomentReciprocalSqrtLog n)
      Filter.atTop (nhds 0) := by
    simpa using (hlogInv.const_mul 2).add hslackInv
  refine ⟨hslack, ?_⟩
  apply hsum.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  let L : ℝ := Real.log (n : ℝ)
  let s : ℝ := Real.sqrt L
  have hL : 0 < L := Real.log_pos hnR
  have hspos : 0 < s := Real.sqrt_pos.2 hL
  have hsq : s * s = L := Real.mul_self_sqrt hL.le
  change 2 * L⁻¹ + s⁻¹ = (2 + s) / L
  rw [← hsq]
  field_simp [ne_of_gt hspos]

/-- The normalized upper envelope admits an exact rational representation
once `n >= 2`.  No asymptotic or probability assumptions enter this identity. -/
theorem correctedNormalizedMomentEnvelope_eq_rational
    (D : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    correctedNormalizedMomentEnvelope D n =
      correctedNormalizedMomentRational D
        (correctedMomentReciprocalSqrtLog n) := by
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  let L : ℝ := Real.log (n : ℝ)
  let s : ℝ := Real.sqrt L
  have hL : 0 < L := Real.log_pos hnR
  have hs : 0 < s := Real.sqrt_pos.2 hL
  have hsq : s * s = L := Real.mul_self_sqrt hL.le
  have hα : 0 < 2 + s := by linarith
  have hαone : 1 < 2 + s := by linarith
  have hfactor : 0 < 1 - 1 / (2 + s) := by
    have hdiv : (1 : ℝ) / (2 + s) < 1 := by
      apply (div_lt_iff₀ hα).2
      linarith
    linarith
  have hones : 1 + s ≠ 0 := ne_of_gt (by linarith)
  have honeinv : 1 + s⁻¹ ≠ 0 := ne_of_gt (by
    have hinv : 0 < s⁻¹ := inv_pos.mpr hs
    linarith)
  change (1 + L + (2 + s) * D) / ((1 - 1 / (2 + s)) * L) =
      ((1 + D * s⁻¹ + (1 + 2 * D) * (s⁻¹) ^ 2) *
        (1 + 2 * s⁻¹)) / (1 + s⁻¹)
  rw [← hsq]
  field_simp [ne_of_gt hs, ne_of_gt hα, ne_of_gt hfactor,
    hones, honeinv]
  -- Clearing the displayed fractions leaves a factor `(1 + s)⁻¹`.
  -- Multiply the genuine inverse cancellation by the right-hand polynomial;
  -- ring normalization then matches the complete residual identity.
  have hcancel : (1 + s)⁻¹ * (1 + s) = (1 : ℝ) :=
    inv_mul_cancel₀ hones
  have hscaled :
      (2 + s + s * D * 4 + s ^ 2 * 2 + s ^ 2 * D + s ^ 3 + D * 4) *
          ((1 + s)⁻¹ * (1 + s)) =
        2 + s + s * D * 4 + s ^ 2 * 2 + s ^ 2 * D + s ^ 3 + D * 4 := by
    rw [hcancel, mul_one]
  ring_nf at hscaled ⊢
  exact hscaled

/-- The normalized *upper envelope* converges to one with a uniformly
bounded moment-ratio parameter. This does not say that the expected runtime
ratio converges to one. -/
theorem correctedNormalizedMomentEnvelope_tendsto_one (D : ℝ) :
    Filter.Tendsto (correctedNormalizedMomentEnvelope D)
      Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto
      (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have ht : Filter.Tendsto correctedMomentReciprocalSqrtLog
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hs
  have hnum : ContinuousAt
      (fun t : ℝ => (1 + D * t + (1 + 2 * D) * t ^ 2) *
        (1 + 2 * t)) 0 := by fun_prop
  have hden : ContinuousAt (fun t : ℝ => 1 + t) 0 := by fun_prop
  have hrational : ContinuousAt
      (correctedNormalizedMomentRational D) 0 := by
    unfold correctedNormalizedMomentRational
    exact hnum.div hden (by norm_num)
  have hzero : correctedNormalizedMomentRational D 0 = 1 := by
    norm_num [correctedNormalizedMomentRational]
  have hlim : Filter.Tendsto
      (fun n : ℕ =>
        correctedNormalizedMomentRational D
          (correctedMomentReciprocalSqrtLog n))
      Filter.atTop (nhds 1) := by
    have hcomp := hrational.tendsto.comp ht
    rw [hzero] at hcomp
    simpa only [Function.comp_def] using hcomp
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact (correctedNormalizedMomentEnvelope_eq_rational D hn).symm

/-- A dimension-free upper bound on the product of the first and second
factorial radius moments, normalized by squared one-bit mass. -/
theorem momentRatio_le_uniform_bound
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    {p₀ C₁ C₂ : ℝ} (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ law.oneBitMass)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hmean : law.meanRadius ≤ C₁)
    (hsecond : law.secondFactorialRadiusMoment ≤ C₂) :
    law.meanRadius * law.secondFactorialRadiusMoment /
        law.oneBitMass ^ 2 ≤ C₁ * C₂ / p₀ ^ 2 := by
  have hp₁pos : 0 < law.oneBitMass := lt_of_lt_of_le hp₀ hp₁
  have hpower : p₀ ^ 2 ≤ law.oneBitMass ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp₁)
      (add_nonneg hp₁pos.le hp₀.le)]
  have hproduct :
      law.meanRadius * law.secondFactorialRadiusMoment ≤ C₁ * C₂ := by
    calc
      law.meanRadius * law.secondFactorialRadiusMoment ≤
          C₁ * law.secondFactorialRadiusMoment :=
        mul_le_mul_of_nonneg_right hmean law.secondFactorialRadiusMoment_nonneg
      _ ≤ C₁ * C₂ := mul_le_mul_of_nonneg_left hsecond hC₁
  apply (div_le_div_iff₀ (pow_pos hp₁pos 2) (pow_pos hp₀ 2)).2
  calc
    (law.meanRadius * law.secondFactorialRadiusMoment) * p₀ ^ 2 ≤
        (C₁ * C₂) * p₀ ^ 2 :=
      mul_le_mul_of_nonneg_right hproduct (sq_nonneg p₀)
    _ ≤ (C₁ * C₂) * law.oneBitMass ^ 2 :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg hC₁ hC₂)

/-- For any fixed nonnegative uniform bound `D` on the normalized radius
moment, the expected runtime is eventually at most `(1+epsilon) n log n/p₁`.
The threshold is uniform in the dimension-specific law, objective and state. -/
theorem correctedLinearPotential_runtimeSup_le_sharpUpper_of_ratio_bound
    {D epsilon : ℝ} (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ (law : StaticUnaryUnbiasedMutation n),
        0 < law.oneBitMass →
        law.meanRadius * law.secondFactorialRadiusMoment /
            law.oneBitMass ^ 2 ≤ D →
        ∀ (w : Fin n → ℝ), PositiveLinearWeights w →
          NonincreasingLinearWeights w → ∀ (x : BitString n),
        runtimeSup (law.transition (linearFitness w))
          ({allOnes n} : Set (BitString n)) x ≤
        ENNReal.ofReal
          ((1 + epsilon) * ((n : ℝ) * Real.log (n : ℝ) /
            law.oneBitMass)) := by
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      correctedNormalizedMomentEnvelope D n < 1 + epsilon :=
    (correctedNormalizedMomentEnvelope_tendsto_one D).eventually
      (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + epsilon))
  have hall := hevent.and (Filter.eventually_ge_atTop (2 : ℕ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hall
  refine ⟨N, ?_⟩
  intro n hnN law hp₁ hratio w hw hmono x
  obtain ⟨henv, hn⟩ := hN n hnN
  let alpha : ℝ := correctedMomentSlack n
  let L : ℝ := Real.log (n : ℝ)
  have halpha : 1 < alpha := one_lt_correctedMomentSlack n
  have halpha0 : 0 ≤ alpha := by linarith
  have halphapos : 0 < alpha := by linarith
  have hfactor : 0 < 1 - 1 / alpha := by
    have hdiv : (1 : ℝ) / alpha < 1 := by
      apply (div_lt_iff₀ halphapos).2
      simpa using halpha
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < L := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  have hden : 0 < law.oneBitMass * (1 - 1 / alpha) :=
    mul_pos hp₁ hfactor
  have hprefix : 0 ≤ (n : ℝ) / (law.oneBitMass * (1 - 1 / alpha)) :=
    div_nonneg hnR.le hden.le
  have hbase := law.correctedLinearPotential_runtimeSup_le_explicit
    hn hp₁ halpha w hw hmono x
  have hmoment :
      alpha * law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 ≤ alpha * D := by
    have hm := mul_le_mul_of_nonneg_left hratio halpha0
    calc
      alpha * law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 =
        alpha * (law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2) := by ring
      _ ≤ alpha * D := hm
  have hscale : 0 ≤ (n : ℝ) * L / law.oneBitMass :=
    div_nonneg (mul_nonneg hnR.le hlog.le) hp₁.le
  have hrewrite :
      ((n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))) *
          (1 + L + alpha * D) =
        ((n : ℝ) * L / law.oneBitMass) *
          correctedNormalizedMomentEnvelope D n := by
    change ((n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))) *
        (1 + L + alpha * D) =
      ((n : ℝ) * L / law.oneBitMass) *
        ((1 + L + alpha * D) / ((1 - 1 / alpha) * L))
    field_simp [ne_of_gt hp₁, ne_of_gt halphapos,
      ne_of_gt hfactor, ne_of_gt hlog]
  have hreal :
      ((n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))) *
          (1 + L + alpha * law.meanRadius *
            law.secondFactorialRadiusMoment / law.oneBitMass ^ 2) ≤
        (1 + epsilon) * ((n : ℝ) * L / law.oneBitMass) := by
    calc
      _ ≤ ((n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))) *
            (1 + L + alpha * D) :=
        mul_le_mul_of_nonneg_left (by linarith) hprefix
      _ = ((n : ℝ) * L / law.oneBitMass) *
            correctedNormalizedMomentEnvelope D n := hrewrite
      _ ≤ ((n : ℝ) * L / law.oneBitMass) * (1 + epsilon) :=
        mul_le_mul_of_nonneg_left henv.le hscale
      _ = (1 + epsilon) * ((n : ℝ) * L / law.oneBitMass) := by ring
  exact hbase.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The epsilon-sharp upper certificate with the original Stage-86 *uniform*
`p₀`, `C₁`, `C₂` assumptions.  No lower bound and no mean-only reduction is
included in the conclusion. -/
theorem correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments
    {p₀ C₁ C₂ epsilon : ℝ}
    (hp₀ : 0 < p₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ (law : StaticUnaryUnbiasedMutation n),
        p₀ ≤ law.oneBitMass →
        law.meanRadius ≤ C₁ →
        law.secondFactorialRadiusMoment ≤ C₂ →
        ∀ (w : Fin n → ℝ), PositiveLinearWeights w →
          NonincreasingLinearWeights w → ∀ (x : BitString n),
        runtimeSup (law.transition (linearFitness w))
          ({allOnes n} : Set (BitString n)) x ≤
        ENNReal.ofReal
          ((1 + epsilon) * ((n : ℝ) * Real.log (n : ℝ) /
            law.oneBitMass)) := by
  have hD : 0 ≤ C₁ * C₂ / p₀ ^ 2 :=
    div_nonneg (mul_nonneg hC₁ hC₂) (sq_nonneg p₀)
  obtain ⟨N, hN⟩ := correctedLinearPotential_runtimeSup_le_sharpUpper_of_ratio_bound
    hD hepsilon
  refine ⟨N, ?_⟩
  intro n hn law hp₁ hmean hsecond w hw hmono x
  have hp₁pos : 0 < law.oneBitMass := lt_of_lt_of_le hp₀ hp₁
  have hratio := law.momentRatio_le_uniform_bound
    hp₀ hp₁ hC₁ hC₂ hmean hsecond
  exact hN n hn law hp₁pos hratio w hw hmono x

end StaticUnaryUnbiasedMutation
end ECRuntime
