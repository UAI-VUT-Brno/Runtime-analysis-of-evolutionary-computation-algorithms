import ECRuntime.WittMutationRuntime
import ECRuntime.WittStandardRuntimeTailShift
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 48: high-probability fixed-scale Witt runtime endpoint

Stage 47 closes the fixed-scale expectation layer on the verified mutation-rate regime
`p = c/n`, `0 < c <= 1`, `n >= 4`.  This module reuses the already compiler-promoted
generic multiplicative-drift survival theorem to obtain the matching sample-path tail.
No C2/C3, selection, or drift argument is reopened.

Writing

`q_n(c) = scaledLinearSingletonRate c n`,

the exact natural-threshold geometric estimate is

`P(T > k) <= e n * (1 - q_n(c))^k`.

The generic elementary conversion from Stage 41 then yields an exact-rate shifted tail
under

`q_n(c)^(-1) * (1 + log n + r) <= k`.

Finally, Stage 47 proved the finite inverse-rate inequality

`q_n(c)^(-1) <= (exp(c)/c) n`.

For `r >= 0`, this gives the literature-facing fixed-scale threshold

`(exp(c)/c) n (1 + log n + r) <= k`

and hence `P(T > k) <= exp(-r)`.
-/

/-- Infinite trajectory law of the `(1+1)` EA with scaled mutation rate `p=c/n` on an
arbitrary linear objective, restricted to the currently verified regime. -/
noncomputable def linearScaledTrajectoryMeasure
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) : Measure (ℕ → BitString n) :=
  transitionTrajectoryMeasure
    (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
    (onePlusOneTransition_stochastic
      (scaledMutationRate_nonneg hc0)
      (scaledMutationRate_le_one (by omega : 0 < n) (by
        have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (show 1 ≤ n by omega)
        exact hc1.trans hnreal))
      (linearFitness w))
    x

/-- The exact scaled singleton drift rate is at most one on the verified interval. -/
theorem scaledLinearSingletonRate_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    scaledLinearSingletonRate c n ≤ 1 := by
  have hnpos : 0 < n := by omega
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hcn : c ≤ (n : ℝ) := hc1.trans hnreal
  have hp0 : 0 ≤ scaledMutationRate c n := scaledMutationRate_nonneg hc0
  have hp1 : scaledMutationRate c n ≤ 1 :=
    scaledMutationRate_le_one hnpos hcn
  unfold scaledLinearSingletonRate linearSingletonRate
  have hq0 : 0 ≤ 1 - scaledMutationRate c n := by linarith
  have hq1 : 1 - scaledMutationRate c n ≤ 1 := by linarith
  have hpow :
      (1 - scaledMutationRate c n) ^ (n - 1) ≤ 1 :=
    pow_le_one₀ hq0 hq1
  calc
    scaledMutationRate c n * (1 - scaledMutationRate c n) ^ (n - 1) ≤
        scaledMutationRate c n * 1 :=
      mul_le_mul_of_nonneg_left hpow hp0
    _ = scaledMutationRate c n := by ring
    _ ≤ 1 := hp1

/-- Natural-threshold geometric tail for the conventional optimization time at the
scaled mutation rate `p=c/n`. -/
theorem wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n) (k : ℕ) :
    runtimeTailMass
        (linearScaledTrajectoryMeasure hn hc0.le hc1 w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal
        ((Real.exp 1 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k) := by
  have hnpos : 0 < n := by omega
  have hp0 : 0 < scaledMutationRate c n :=
    scaledMutationRate_pos hc0 hnpos
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one
    hn hc0.le hc1
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt hp_le (standardMutationRate_lt_one (by omega : 2 ≤ n))
  let P := onePlusOneTransition (scaledMutationRate c n) (linearFitness w)
  let V := wittMutationLinearPotential (scaledMutationRate c n) w
  have hP : IsStochastic P := by
    dsimp [P]
    exact onePlusOneTransition_stochastic hp0.le hp1.le (linearFitness w)
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget V → (1 : ℝ) ≤ V z := by
    intro z hz
    dsimp [V]
    apply one_le_wittMutationLinearPotential_of_ne_allOnes hp0.le hp1 w z
    intro hall
    apply hz
    change wittMutationLinearPotential (scaledMutationRate c n) w z = 0
    rw [hall]
    exact wittMutationLinearPotential_allOnes (scaledMutationRate c n) w
  have hxTarget : x ∉ realPotentialTarget V := by
    intro hxt
    have hx0 : V x = 0 := by
      simpa [realPotentialTarget] using hxt
    apply hx
    dsimp [V] at hx0
    exact (wittMutationLinearPotential_eq_zero_iff hp0.le hp1 w x).mp hx0
  have hδ0 : 0 ≤ scaledLinearSingletonRate c n := by
    simpa [scaledLinearSingletonRate] using
      (linearSingletonRate_pos hp0 hp1).le
  have hδ1 : scaledLinearSingletonRate c n ≤ 1 :=
    scaledLinearSingletonRate_le_one hn hc0.le hc1
  have htail := multiplicativeDrift_firstHittingTime_tailMass_le
    P hP V (scaledLinearSingletonRate c n) 1
    hδ0 hδ1 (by norm_num)
    hmin
    (by
      dsimp [P, V]
      simpa [scaledLinearSingletonRate] using
        (wittMutation_hasMultiplicativeDriftLowerBound_scaled_of_le_one
          hn hc0.le hc1 w hw hmono))
    x hxTarget k
  have htarget : realPotentialTarget V = oneMaxTarget n := by
    dsimp [V]
    exact wittMutationLinearTarget_eq_oneMaxTarget_scaled hc0.le hp1 w
  have hhit :
      transitionTrajectoryFirstHittingTime (realPotentialTarget V) x =
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x :=
    transitionTrajectoryFirstHittingTime_congr_set
      (realPotentialTarget V) (oneMaxTarget n) htarget x
  have hVupper : V x ≤ Real.exp 1 * (n : ℝ) := by
    dsimp [V]
    exact wittMutationLinearPotential_scaled_le_en hn hc0.le hc1 w x
  have hq : 0 ≤ 1 - scaledLinearSingletonRate c n :=
    sub_nonneg.mpr hδ1
  have hscale :
      (1 : ℝ)⁻¹ * V x * (1 - scaledLinearSingletonRate c n) ^ k ≤
        (Real.exp 1 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k := by
    norm_num
    exact mul_le_mul_of_nonneg_right hVupper (pow_nonneg hq k)
  unfold linearScaledTrajectoryMeasure
  rw [← hhit]
  exact htail.trans (ENNReal.ofReal_le_ofReal hscale)

/-- Exact-rate shifted exponential tail.  This statement keeps the natural threshold in
terms of the reciprocal singleton rate and therefore needs no sign condition on `r`. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (k : ℕ)
    (hk : (scaledLinearSingletonRate c n)⁻¹ *
        (1 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasure hn hc0.le hc1 w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  let A : ℝ := Real.exp 1 * (n : ℝ)
  let δ : ℝ := scaledLinearSingletonRate c n
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos (Real.exp_pos 1) hnrealpos
  have hlogA : Real.log A = 1 + Real.log (n : ℝ) := by
    dsimp [A]
    exact wittStandard_log_en hnpos
  have hp0 : 0 < scaledMutationRate c n :=
    scaledMutationRate_pos hc0 hnpos
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one
    hn hc0.le hc1
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt hp_le (standardMutationRate_lt_one (by omega : 2 ≤ n))
  have hδpos : 0 < δ := by
    dsimp [δ, scaledLinearSingletonRate]
    exact linearSingletonRate_pos hp0 hp1
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact scaledLinearSingletonRate_le_one hn hc0.le hc1
  have hthreshold0 :
      1 + Real.log (n : ℝ) + r ≤ δ * (k : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hk hδpos.le
    dsimp [δ] at hscaled ⊢
    have hδne : scaledLinearSingletonRate c n ≠ 0 := by
      exact ne_of_gt (by
        simpa [scaledLinearSingletonRate] using
          (linearSingletonRate_pos hp0 hp1))
    calc
      1 + Real.log (n : ℝ) + r =
          scaledLinearSingletonRate c n *
            ((scaledLinearSingletonRate c n)⁻¹ *
              (1 + Real.log (n : ℝ) + r)) := by
        field_simp [hδne]
      _ ≤ scaledLinearSingletonRate c n * (k : ℝ) := hscaled
  have hthreshold : Real.log A + r ≤ δ * (k : ℝ) := by
    rw [hlogA]
    exact hthreshold0
  have hreal : A * (1 - δ) ^ k ≤ Real.exp (-r) :=
    geometricPrefactorPow_le_exp_neg_of_log_add_le
      hApos hδ1 k r hthreshold
  have hgeo := wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_le_one
    hn hc0 hc1 w hw hmono x hx k
  have hreal' :
      (Real.exp 1 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k ≤ Real.exp (-r) := by
    change A * (1 - δ) ^ k ≤ Real.exp (-r)
    exact hreal
  exact hgeo.trans (ENNReal.ofReal_le_ofReal hreal')

/-- Literature-facing shifted tail with the finite Stage-47 coefficient
`(exp(c)/c) n`.  The usual high-probability parameter is taken nonnegative. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_scaled_of_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (hr : 0 ≤ r) (k : ℕ)
    (hk : (wittMutationLeadingRuntimeFactor c * (n : ℝ)) *
        (1 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasure hn hc0.le hc1 w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hfactor : 0 ≤ 1 + Real.log (n : ℝ) + r := by
    linarith
  have hrate := scaledLinearSingletonRate_inv_le_leadingFactor_mul_n
    hn hc0 hc1
  have hexact :
      (scaledLinearSingletonRate c n)⁻¹ *
          (1 + Real.log (n : ℝ) + r) ≤ (k : ℝ) := by
    calc
      (scaledLinearSingletonRate c n)⁻¹ *
          (1 + Real.log (n : ℝ) + r) ≤
        (wittMutationLeadingRuntimeFactor c * (n : ℝ)) *
          (1 + Real.log (n : ℝ) + r) :=
        mul_le_mul_of_nonneg_right hrate hfactor
      _ ≤ (k : ℝ) := hk
  exact wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate
    hn hc0 hc1 w hw hmono x hx r k hexact

end ECRuntime
