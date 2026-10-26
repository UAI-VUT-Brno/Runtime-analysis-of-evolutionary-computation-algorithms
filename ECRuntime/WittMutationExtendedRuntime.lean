import ECRuntime.WittMutationC3ExtendedRegime
import ECRuntime.WittMutationCertifiedRuntime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
open Filter
open Asymptotics

namespace ECRuntime

/-!
# Stage 50: runtime and tail endpoints on the extended certified scale interval

Stage 49 extends the exact-singleton-rate Witt drift theorem from `0 <= c <= 1` to the
uniform finite interval

`0 <= c <= wittMutationC3CertifiedScale = 21/20`, `n >= 4`.

This module propagates that wider drift regime through the expectation and
high-probability layers without modifying any compiler-promoted Stage 45--49 source.
The key observation is that the exact C3 envelope already gives a convenient global
bound on the reciprocal-survival power.  From

`base^(n-1) - (1-p) <= 2`

and `0 <= p`, one obtains simply

`base^(n-1) <= 3`.

Consequently, throughout the certified interval,

`V_p(x) <= 3 n`

and, for `p = c/n` with `c > 0`,

`(linearSingletonRate n p)^(-1) <= (3/c) n`.

The exact-rate expectation certificate therefore satisfies

`runtime <= rate^(-1) * (1 + log 3 + log n)`,

and the completely explicit finite envelope is

`runtime <= (3/c) n * (1 + log 3 + log n)`.

The same potential bound yields the geometric tail

`P(T > k) <= 3 n (1-rate)^k`

and the shifted exponential consequence

`(3/c) n (log 3 + log n + r) <= k  ==>  P(T > k) <= exp(-r)`

for `r >= 0`.

These constants are intentionally conservative: Stage 50 is a regime-propagation
layer.  The sharp fixed-`c` factor remains governed asymptotically by the exact singleton
rate and can be recovered after the rate-asymptotic theorem is widened beyond `c <= 1`.
-/

/-- Every scaled mutation rate below the Stage-49 certified endpoint is strictly below
one in dimension at least four. -/
theorem scaledMutationRate_lt_one_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc : c ≤ wittMutationC3CertifiedScale) :
    scaledMutationRate c n < 1 := by
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
  exact lt_of_le_of_lt hpq hq1

/-- On the full Stage-49 certified scale interval the parameterized Witt potential is
bounded uniformly by `3 n`. -/
theorem wittMutationLinearPotential_scaled_le_three_mul_n_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential (scaledMutationRate c n) w x ≤
      3 * (n : ℝ) := by
  have hp1 : scaledMutationRate c n < 1 :=
    scaledMutationRate_lt_one_of_le_certifiedScale hn hc
  have henv :=
    wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0 hc
  exact wittMutationLinearPotential_scaled_le_three_mul_n_of_c3Envelope
    (show 1 ≤ n by omega) hc0 hp1 henv w x

/-- The exact singleton drift rate is at most one on the full certified interval. -/
theorem scaledLinearSingletonRate_le_one_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3CertifiedScale) :
    scaledLinearSingletonRate c n ≤ 1 := by
  exact scaledLinearSingletonRate_le_one_of_lt_one hc0
    (scaledMutationRate_lt_one_of_le_certifiedScale hn hc)

/-- The Stage-49 drift theorem plugged into the generic multiplicative-drift runtime
certificate on the full certified scale interval. -/
theorem wittMutation_runtimeSup_le_certificate_scaled_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
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
  have hp1 : scaledMutationRate c n < 1 :=
    scaledMutationRate_lt_one_of_le_certifiedScale hn hc
  have henv :=
    wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc
  exact wittMutation_runtimeSup_le_certificate_scaled_of_c3Envelope
    (show 1 ≤ n by omega) hc0 hp1 henv w hw hmono x

/-- The exact runtime certificate on the full certified interval is controlled by the
reciprocal singleton rate times `1 + log 3 + log n`. -/
theorem wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (x : BitString n) :
    multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1
        (wittMutationLinearPotential (scaledMutationRate c n) w) x ≤
      (scaledLinearSingletonRate c n)⁻¹ *
        (1 + Real.log 3 + Real.log (n : ℝ)) := by
  have hp1 : scaledMutationRate c n < 1 :=
    scaledMutationRate_lt_one_of_le_certifiedScale hn hc
  have henv :=
    wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc
  exact wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_of_c3Envelope
    (show 1 ≤ n by omega) hc0 hp1 henv w x

/-- The exact reciprocal singleton rate is bounded by `(3/c) n` throughout the
certified interval. This is a finite-dimensional consequence of the same C3 envelope,
not an asymptotic estimate. -/
theorem scaledLinearSingletonRate_inv_le_three_div_scale_mul_n
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale) :
    (scaledLinearSingletonRate c n)⁻¹ ≤
      (3 / c) * (n : ℝ) := by
  have hp1 : scaledMutationRate c n < 1 :=
    scaledMutationRate_lt_one_of_le_certifiedScale hn hc
  have henv :=
    wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc
  exact scaledLinearSingletonRate_inv_le_three_div_scale_mul_n_of_c3Envelope
    (show 1 ≤ n by omega) hc0 hp1 henv

/-- Explicit coefficient-independent runtime bound on the full Stage-49 certified
interval. -/
theorem wittMutation_runtimeSup_le_certifiedScale_log_bound
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (((3 / c) * (n : ℝ)) *
          (1 + Real.log 3 + Real.log (n : ℝ))) := by
  exact wittMutation_runtimeSup_le_log_bound_of_c3Envelope
    (show 1 ≤ n by omega) hc0
    (scaledMutationRate_lt_one_of_le_certifiedScale hn hc)
    (wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc)
    w hw hmono x

/-- Named finite upper envelope for the extended certified regime. -/
noncomputable def wittMutationCertifiedRuntimeUpperBound (c : ℝ) (n : ℕ) : ℝ :=
  ((3 / c) * (n : ℝ)) *
    (1 + Real.log 3 + Real.log (n : ℝ))

/-- Leading `3/c * n log n` term of the conservative certified-regime envelope. -/
noncomputable def wittMutationCertifiedRuntimeLeadingTerm (c : ℝ) (n : ℕ) : ℝ :=
  (3 / c) * natLinearLogGrowth n

/-- Linear correction of the conservative certified-regime envelope. -/
noncomputable def wittMutationCertifiedRuntimeLinearCorrection
    (c : ℝ) (n : ℕ) : ℝ :=
  ((3 / c) * (1 + Real.log 3)) * natLinearGrowth n

/-- Exact decomposition of the certified-regime finite runtime envelope. -/
theorem wittMutationCertifiedRuntimeUpperBound_eq_leading_add_linear
    (c : ℝ) (n : ℕ) :
    wittMutationCertifiedRuntimeUpperBound c n =
      wittMutationCertifiedRuntimeLeadingTerm c n +
        wittMutationCertifiedRuntimeLinearCorrection c n := by
  unfold wittMutationCertifiedRuntimeUpperBound
    wittMutationCertifiedRuntimeLeadingTerm
    wittMutationCertifiedRuntimeLinearCorrection
    natLinearLogGrowth natLinearGrowth
  ring

/-- For fixed positive scale, the correction in the certified-regime envelope is
`O(n)`. -/
theorem wittMutationCertifiedRuntimeLinearCorrection_isBigO
    (c : ℝ) :
    NatIsBigO (wittMutationCertifiedRuntimeLinearCorrection c) natLinearGrowth := by
  unfold wittMutationCertifiedRuntimeLinearCorrection
  exact Asymptotics.isBigO_const_mul_self
    ((3 / c) * (1 + Real.log 3)) natLinearGrowth Filter.atTop

/-- Formal `3/c * n log n + O(n)` decomposition of the conservative finite envelope. -/
theorem wittMutationCertifiedRuntimeUpperBound_eq_leading_add_bigO_n
    (c : ℝ) :
    ∃ r : ℕ → ℝ,
      NatIsBigO r natLinearGrowth ∧
      ∀ n : ℕ,
        wittMutationCertifiedRuntimeUpperBound c n =
          wittMutationCertifiedRuntimeLeadingTerm c n + r n := by
  refine ⟨wittMutationCertifiedRuntimeLinearCorrection c,
    wittMutationCertifiedRuntimeLinearCorrection_isBigO c, ?_⟩
  intro n
  exact wittMutationCertifiedRuntimeUpperBound_eq_leading_add_linear c n

/-- Runtime theorem through the named Stage-50 certified-regime upper envelope. -/
theorem wittMutation_runtimeSup_le_certifiedScale_upperBound
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (wittMutationCertifiedRuntimeUpperBound c n) := by
  unfold wittMutationCertifiedRuntimeUpperBound
  exact wittMutation_runtimeSup_le_certifiedScale_log_bound
    hn hc0 hc w hw hmono x

/-! ## High-probability endpoint on the certified interval -/

/-- Infinite trajectory law on the retained `21/20` compatibility interval. -/
noncomputable def linearScaledTrajectoryMeasureCertified
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) : Measure (ℕ → BitString n) :=
  linearScaledTrajectoryMeasureOfLtOne hc0
    (scaledMutationRate_lt_one_of_le_certifiedScale hn hc) w x

/-- Natural-threshold geometric tail on the retained certified compatibility interval. -/
theorem wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_le_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n) (k : ℕ) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureCertified hn hc0.le hc w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal
        ((3 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k) := by
  simpa [linearScaledTrajectoryMeasureCertified] using
    (wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_c3Envelope
      (show 1 ≤ n by omega) hc0
      (scaledMutationRate_lt_one_of_le_certifiedScale hn hc)
      (wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc)
      w hw hmono x hx k)

/-- Exact-rate shifted exponential tail on the retained certified compatibility interval. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (k : ℕ)
    (hk : (scaledLinearSingletonRate c n)⁻¹ *
        (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureCertified hn hc0.le hc w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  simpa [linearScaledTrajectoryMeasureCertified] using
    (wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate_of_c3Envelope
      (show 1 ≤ n by omega) hc0
      (scaledMutationRate_lt_one_of_le_certifiedScale hn hc)
      (wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc)
      w hw hmono x hx r k hk)

/-- Completely explicit shifted tail on the retained certified compatibility interval. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_certifiedScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3CertifiedScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (hr : 0 ≤ r) (k : ℕ)
    (hk : ((3 / c) * (n : ℝ)) *
        (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureCertified hn hc0.le hc w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  simpa [linearScaledTrajectoryMeasureCertified] using
    (wittMutation_firstHittingTime_tailMass_le_exp_shifted_of_c3Envelope
      (show 1 ≤ n by omega) hc0
      (scaledMutationRate_lt_one_of_le_certifiedScale hn hc)
      (wittMutationC3EnvelopeCondition_scaled_of_le_certifiedScale hn hc0.le hc)
      w hw hmono x hx r hr k hk)

end ECRuntime
