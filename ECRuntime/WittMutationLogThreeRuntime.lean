import ECRuntime.WittMutationC3LogThreeRegime
import ECRuntime.WittMutationCertifiedRuntime
import ECRuntime.WittMutationSharpRuntimeAsymptotics
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
open Filter
open Asymptotics

namespace ECRuntime

/-!
# Runtime and tail consequences on the exact log-three C3 interval

Stage 66 closes the finite C3 condition analytically on the natural interval

`0 <= c <= log 3`, `n >= 4`.

This module is the single downstream adapter for that final C3 boundary.  It deliberately
contains no endpoint-specific drift proof: all expectation and tail statements are obtained by
instantiating `WittMutationCertifiedRuntime` with the Stage-66 envelope theorem.  The exact-rate
asymptotic layer remains unchanged and supplies the sharp fixed-scale leading coefficient
`exp(c) / c`.
-/

/-- On the full log-three interval the Witt potential is uniformly bounded by `3 n`. -/
theorem wittMutationLinearPotential_scaled_le_three_mul_n_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential (scaledMutationRate c n) w x ≤ 3 * (n : ℝ) := by
  have hp1 := scaledMutationRate_lt_one_of_le_logThreeScale hn hc
  have henv :=
    wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0 hc
  exact wittMutationLinearPotential_scaled_le_three_mul_n_of_c3Envelope
    (show 1 ≤ n by omega) hc0 hp1 henv w x

/-- The exact singleton drift rate is at most one on the full log-three interval. -/
theorem scaledLinearSingletonRate_le_one_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3LogThreeScale) :
    scaledLinearSingletonRate c n ≤ 1 := by
  exact scaledLinearSingletonRate_le_one_of_lt_one hc0
    (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)

/-- Generic multiplicative-drift runtime certificate specialized to `0 < c <= log 3`. -/
theorem wittMutation_runtimeSup_le_certificate_scaled_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
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
  exact wittMutation_runtimeSup_le_certificate_scaled_of_c3Envelope
    (show 1 ≤ n by omega) hc0
    (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
    (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)
    w hw hmono x

/-- The exact-rate runtime certificate is controlled by
`q_n(c)^(-1) * (1 + log 3 + log n)` on the full log-three interval. -/
theorem wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (x : BitString n) :
    multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1
        (wittMutationLinearPotential (scaledMutationRate c n) w) x ≤
      (scaledLinearSingletonRate c n)⁻¹ *
        (1 + Real.log 3 + Real.log (n : ℝ)) := by
  exact wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_of_c3Envelope
    (show 1 ≤ n by omega) hc0
    (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
    (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)
    w x

/-- The reciprocal singleton rate is bounded by `(3/c) n` on the full log-three interval. -/
theorem scaledLinearSingletonRate_inv_le_three_div_scale_mul_n_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale) :
    (scaledLinearSingletonRate c n)⁻¹ ≤ (3 / c) * (n : ℝ) := by
  exact scaledLinearSingletonRate_inv_le_three_div_scale_mul_n_of_c3Envelope
    (show 1 ≤ n by omega) hc0
    (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
    (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)

/-- Explicit finite expectation bound throughout `0 < c <= log 3`. -/
theorem wittMutation_runtimeSup_le_logThreeScale_log_bound
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
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
    (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
    (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)
    w hw hmono x

/-- Exact-rate expectation envelope on the full log-three interval. -/
theorem wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (wittMutationExactRateRuntimeUpperBound c n) := by
  have hcert :=
    wittMutation_runtimeSup_le_certificate_scaled_of_le_logThreeScale
      hn hc0 hc w hw hmono x
  have hmult :=
    wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_logThreeScale
      hn hc0 hc w x
  unfold wittMutationExactRateRuntimeUpperBound
  exact hcert.trans (ENNReal.ofReal_le_ofReal hmult)

/-- The normalized exact-rate envelope has sharp fixed-scale leading coefficient `exp(c)/c`
throughout the log-three interval. -/
theorem wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_logThreeScale
    {c : ℝ} (hc0 : 0 < c) (_hc : c ≤ wittMutationC3LogThreeScale) :
    Filter.Tendsto
      (fun n : ℕ => wittMutationExactRateNormalizedRuntimeUpperBound c n)
      Filter.atTop (nhds (wittMutationLeadingRuntimeFactor c)) := by
  exact wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_leadingFactor hc0

/-- On the full log-three interval, the sharp exact-rate leading coefficient is minimized at
`c = 1`. -/
theorem wittMutationExactRateRuntimeLeadingFactor_one_le_logThreeScale
    {c : ℝ} (hc0 : 0 < c) (_hc : c ≤ wittMutationC3LogThreeScale) :
    wittMutationLeadingRuntimeFactor 1 ≤ wittMutationLeadingRuntimeFactor c := by
  exact wittMutationLeadingRuntimeFactor_one_le_fixed hc0

/-! ## High-probability runtime on the final C3 interval -/

/-- Infinite trajectory law on the full log-three interval. -/
noncomputable def linearScaledTrajectoryMeasureLogThree
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) : Measure (ℕ → BitString n) :=
  linearScaledTrajectoryMeasureOfLtOne hc0
    (scaledMutationRate_lt_one_of_le_logThreeScale hn hc) w x

/-- Natural-threshold geometric runtime tail on the full log-three interval. -/
theorem wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_le_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n) (k : ℕ) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureLogThree hn hc0.le hc w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal
        ((3 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k) := by
  simpa [linearScaledTrajectoryMeasureLogThree] using
    (wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_c3Envelope
      (show 1 ≤ n by omega) hc0
      (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
      (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)
      w hw hmono x hx k)

/-- Exact-singleton-rate shifted exponential tail on the full log-three interval. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (k : ℕ)
    (hk : (scaledLinearSingletonRate c n)⁻¹ *
        (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureLogThree hn hc0.le hc w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  simpa [linearScaledTrajectoryMeasureLogThree] using
    (wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate_of_c3Envelope
      (show 1 ≤ n by omega) hc0
      (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
      (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)
      w hw hmono x hx r k hk)

/-- Completely explicit shifted exponential tail on the full log-three interval. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ wittMutationC3LogThreeScale)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (hr : 0 ≤ r) (k : ℕ)
    (hk : ((3 / c) * (n : ℝ)) *
        (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureLogThree hn hc0.le hc w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  simpa [linearScaledTrajectoryMeasureLogThree] using
    (wittMutation_firstHittingTime_tailMass_le_exp_shifted_of_c3Envelope
      (show 1 ≤ n by omega) hc0
      (scaledMutationRate_lt_one_of_le_logThreeScale hn hc)
      (wittMutationC3EnvelopeCondition_scaled_of_le_logThreeScale hn hc0.le hc)
      w hw hmono x hx r hr k hk)

end ECRuntime
