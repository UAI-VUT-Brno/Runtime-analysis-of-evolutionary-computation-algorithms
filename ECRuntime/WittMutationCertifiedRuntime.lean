import ECRuntime.WittMutationC3Envelope
import ECRuntime.WittMutationStrictTail
import ECRuntime.WittMutationRuntimeTail
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
open Filter
open Asymptotics

namespace ECRuntime

/-!
# Runtime consequences of an arbitrary finite C3 certificate

The endpoint-specific runtime modules used to repeat the same proof after every numerical
improvement of the C3 interval.  This file exposes the reusable core instead.  Its statements
assume only the facts the runtime argument actually needs: positivity/admissibility of the
scaled mutation rate and the finite C3 envelope.  Numerical endpoint modules can therefore be
thin adapters.
-/

/-- The exact C3 envelope controls the full reciprocal-survival power by three. -/
theorem wittMutationBase_pow_pred_le_three_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1)
    (henv : WittMutationC3EnvelopeCondition p n) :
    wittMutationBase p ^ (n - 1) ≤ 3 := by
  have hclosed :=
    (wittMutationC3EnvelopeCondition_iff_closedForm hn hp1).mp henv
  linarith

/-- Any scaled C3 certificate yields the uniform potential estimate `V <= 3 n`. -/
theorem wittMutationLinearPotential_scaled_le_three_mul_n_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential (scaledMutationRate c n) w x ≤ 3 * (n : ℝ) := by
  have hp0 : 0 ≤ scaledMutationRate c n := scaledMutationRate_nonneg hc0
  have hpow :
      wittMutationBase (scaledMutationRate c n) ^ (n - 1) ≤ 3 :=
    wittMutationBase_pow_pred_le_three_of_c3Envelope hn hp0 hp1 henv
  have hV := wittMutationLinearPotential_le_n_mul_fullPower hp0 hp1 w x
  calc
    wittMutationLinearPotential (scaledMutationRate c n) w x ≤
        (n : ℝ) * wittMutationBase (scaledMutationRate c n) ^ (n - 1) := hV
    _ ≤ (n : ℝ) * 3 :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
    _ = 3 * (n : ℝ) := by ring

/-- The exact singleton rate is at most one whenever the mutation probability lies in `[0,1)`. -/
theorem scaledLinearSingletonRate_le_one_of_lt_one
    {n : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hp1lt : scaledMutationRate c n < 1) :
    scaledLinearSingletonRate c n ≤ 1 := by
  have hp0 : 0 ≤ scaledMutationRate c n := scaledMutationRate_nonneg hc0
  have hp1 : scaledMutationRate c n ≤ 1 := hp1lt.le
  unfold scaledLinearSingletonRate linearSingletonRate
  have hq0 : 0 ≤ 1 - scaledMutationRate c n := by linarith
  have hq1 : 1 - scaledMutationRate c n ≤ 1 := by linarith
  have hpow : (1 - scaledMutationRate c n) ^ (n - 1) ≤ 1 :=
    pow_le_one₀ hq0 hq1
  calc
    scaledMutationRate c n * (1 - scaledMutationRate c n) ^ (n - 1) ≤
        scaledMutationRate c n * 1 :=
      mul_le_mul_of_nonneg_left hpow hp0
    _ = scaledMutationRate c n := by ring
    _ ≤ 1 := hp1

/-- Runtime certificate obtained directly from a C3 envelope, without naming a numerical endpoint. -/
theorem wittMutation_runtimeSup_le_certificate_scaled_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
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
  have hp0 : 0 < scaledMutationRate c n := scaledMutationRate_pos hc0 hnpos
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
      (wittMutation_hasMultiplicativeDriftLowerBound_of_c3Envelope
        hp0.le hp1 w hw hmono henv)
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
multiplied by `1 + log 3 + log n` under any C3 certificate. -/
theorem wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
    (w : Fin n → ℝ) (x : BitString n) :
    multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1
        (wittMutationLinearPotential (scaledMutationRate c n) w) x ≤
      (scaledLinearSingletonRate c n)⁻¹ *
        (1 + Real.log 3 + Real.log (n : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnrealne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  have hp0 : 0 < scaledMutationRate c n := scaledMutationRate_pos hc0 hnpos
  have hratePos : 0 < scaledLinearSingletonRate c n := by
    simpa [scaledLinearSingletonRate] using (linearSingletonRate_pos hp0 hp1)
  let V := wittMutationLinearPotential (scaledMutationRate c n) w
  let C : ℝ := 3 * (n : ℝ)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hlogC : Real.log C = Real.log 3 + Real.log (n : ℝ) := by
    dsimp [C]
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnrealne]
  change multiplicativeDriftRuntime
      (scaledLinearSingletonRate c n) 1 V x ≤
    (scaledLinearSingletonRate c n)⁻¹ *
      (1 + Real.log 3 + Real.log (n : ℝ))
  by_cases hx0 : V x = 0
  · have hcert : multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1 V x = 0 := by
      unfold multiplicativeDriftRuntime additiveDriftRuntime
      simp [multiplicativeDriftPotential, hx0]
    rw [hcert]
    have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
    exact mul_nonneg (inv_nonneg.mpr hratePos.le) (by linarith)
  · have hxpos : 0 < V x := by
      have hnonneg : 0 ≤ V x := by
        dsimp [V]
        exact wittMutationLinearPotential_nonneg hp0.le hp1 w x
      exact lt_of_le_of_ne hnonneg (Ne.symm hx0)
    have hVupper : V x ≤ C := by
      dsimp [V, C]
      exact wittMutationLinearPotential_scaled_le_three_mul_n_of_c3Envelope
        hn hc0.le hp1 henv w x
    have hlog : Real.log (V x) ≤ Real.log C := Real.log_le_log hxpos hVupper
    have hcert : multiplicativeDriftRuntime
        (scaledLinearSingletonRate c n) 1 V x =
          (scaledLinearSingletonRate c n)⁻¹ * (1 + Real.log (V x)) := by
      have hraw := multiplicativeDriftRuntime_eq_log_ratio
        V (scaledLinearSingletonRate c n) 1 (by norm_num) x hx0
      simpa only [div_one] using hraw
    rw [hcert]
    rw [hlogC] at hlog
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hratePos.le)

/-- The exact reciprocal singleton rate is bounded by `(3/c) n` under any finite C3 certificate. -/
theorem scaledLinearSingletonRate_inv_le_three_div_scale_mul_n_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n) :
    (scaledLinearSingletonRate c n)⁻¹ ≤ (3 / c) * (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnreal_ne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  have hp0 : 0 ≤ scaledMutationRate c n := scaledMutationRate_nonneg hc0.le
  have hpow : wittMutationBase (scaledMutationRate c n) ^ (n - 1) ≤ 3 :=
    wittMutationBase_pow_pred_le_three_of_c3Envelope hn hp0 hp1 henv
  have hp : scaledMutationRate c n = c / (n : ℝ) := scaledMutationRate_eq_div_of_pos hnpos
  have hsurv : 1 - c / (n : ℝ) = ((n : ℝ) - c) / (n : ℝ) := by
    field_simp [hnreal_ne]
  have hbase :
      wittMutationBase (scaledMutationRate c n) = (n : ℝ) / ((n : ℝ) - c) := by
    unfold wittMutationBase
    rw [hp, hsurv, inv_div]
  rw [hbase] at hpow
  have hrate :
      (scaledLinearSingletonRate c n)⁻¹ =
        ((n : ℝ) / c) * (((n : ℝ) / ((n : ℝ) - c)) ^ (n - 1)) := by
    unfold scaledLinearSingletonRate linearSingletonRate
    rw [hp, hsurv]
    rw [mul_inv_rev, ← inv_pow]
    simp only [inv_div]
    ring
  rw [hrate]
  have hpref0 : 0 ≤ (n : ℝ) / c := div_nonneg hnrealpos.le hc0.le
  calc
    ((n : ℝ) / c) * (((n : ℝ) / ((n : ℝ) - c)) ^ (n - 1)) ≤
        ((n : ℝ) / c) * 3 := mul_le_mul_of_nonneg_left hpow hpref0
    _ = (3 / c) * (n : ℝ) := by ring


/-- Explicit finite runtime bound obtained from an arbitrary finite C3 envelope. -/
theorem wittMutation_runtimeSup_le_log_bound_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (((3 / c) * (n : ℝ)) *
          (1 + Real.log 3 + Real.log (n : ℝ))) := by
  have hcert :=
    wittMutation_runtimeSup_le_certificate_scaled_of_c3Envelope
      hn hc0 hp1 henv w hw hmono x
  have hmult :=
    wittMutation_multiplicativeRuntime_le_inverseRate_log_bound_of_c3Envelope
      hn hc0 hp1 henv w x
  have hrate :=
    scaledLinearSingletonRate_inv_le_three_div_scale_mul_n_of_c3Envelope
      hn hc0 hp1 henv
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hfac : 0 ≤ 1 + Real.log 3 + Real.log (n : ℝ) := by linarith
  have hfinite :
      multiplicativeDriftRuntime
          (scaledLinearSingletonRate c n) 1
          (wittMutationLinearPotential (scaledMutationRate c n) w) x ≤
        ((3 / c) * (n : ℝ)) *
          (1 + Real.log 3 + Real.log (n : ℝ)) :=
    hmult.trans (mul_le_mul_of_nonneg_right hrate hfac)
  exact hcert.trans (ENNReal.ofReal_le_ofReal hfinite)

/-! ## High-probability consequences of an arbitrary C3 certificate -/

/-- Infinite trajectory law for a scaled mutation rate already known to lie in `[0,1)`. -/
noncomputable def linearScaledTrajectoryMeasureOfLtOne
    {n : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hp1 : scaledMutationRate c n < 1)
    (w : Fin n → ℝ)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) : Measure (ℕ → BitString n) :=
  transitionTrajectoryMeasure
    (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
    (onePlusOneTransition_stochastic
      (scaledMutationRate_nonneg hc0) hp1.le (linearFitness w))
    x

/-- Natural-threshold geometric tail obtained from an arbitrary finite C3 envelope. -/
theorem wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n) (k : ℕ) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureOfLtOne hc0.le hp1 w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal
        ((3 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k) := by
  have hnpos : 0 < n := by omega
  have hp0 : 0 < scaledMutationRate c n := scaledMutationRate_pos hc0 hnpos
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
    scaledLinearSingletonRate_le_one_of_lt_one hc0.le hp1
  have htail := multiplicativeDrift_firstHittingTime_tailMass_le
    P hP V (scaledLinearSingletonRate c n) 1
    hδ0 hδ1 (by norm_num)
    hmin
    (by
      dsimp [P, V]
      simpa [scaledLinearSingletonRate] using
        (wittMutation_hasMultiplicativeDriftLowerBound_of_c3Envelope
          hp0.le hp1 w hw hmono henv))
    x hxTarget k
  have htarget : realPotentialTarget V = oneMaxTarget n := by
    dsimp [V]
    exact wittMutationLinearTarget_eq_oneMaxTarget_scaled hc0.le hp1 w
  have hhit :
      transitionTrajectoryFirstHittingTime (realPotentialTarget V) x =
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x :=
    transitionTrajectoryFirstHittingTime_congr_set
      (realPotentialTarget V) (oneMaxTarget n) htarget x
  have hVupper : V x ≤ 3 * (n : ℝ) := by
    dsimp [V]
    exact wittMutationLinearPotential_scaled_le_three_mul_n_of_c3Envelope
      hn hc0.le hp1 henv w x
  have hq : 0 ≤ 1 - scaledLinearSingletonRate c n := sub_nonneg.mpr hδ1
  have hscale :
      (1 : ℝ)⁻¹ * V x * (1 - scaledLinearSingletonRate c n) ^ k ≤
        (3 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k := by
    norm_num
    exact mul_le_mul_of_nonneg_right hVupper (pow_nonneg hq k)
  unfold linearScaledTrajectoryMeasureOfLtOne
  rw [← hhit]
  exact htail.trans (ENNReal.ofReal_le_ofReal hscale)

/-- Exact-rate shifted exponential tail obtained from an arbitrary finite C3 envelope. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (k : ℕ)
    (hk : (scaledLinearSingletonRate c n)⁻¹ *
        (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureOfLtOne hc0.le hp1 w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  let A : ℝ := 3 * (n : ℝ)
  let δ : ℝ := scaledLinearSingletonRate c n
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnrealne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hlogA : Real.log A = Real.log 3 + Real.log (n : ℝ) := by
    dsimp [A]
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnrealne]
  have hp0 : 0 < scaledMutationRate c n := scaledMutationRate_pos hc0 hnpos
  have hδpos : 0 < δ := by
    dsimp [δ, scaledLinearSingletonRate]
    exact linearSingletonRate_pos hp0 hp1
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact scaledLinearSingletonRate_le_one_of_lt_one hc0.le hp1
  have hthreshold0 :
      Real.log 3 + Real.log (n : ℝ) + r ≤ δ * (k : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hk hδpos.le
    dsimp [δ] at hscaled ⊢
    have hδne : scaledLinearSingletonRate c n ≠ 0 := by
      exact ne_of_gt (by
        simpa [scaledLinearSingletonRate] using
          (linearSingletonRate_pos hp0 hp1))
    calc
      Real.log 3 + Real.log (n : ℝ) + r =
          scaledLinearSingletonRate c n *
            ((scaledLinearSingletonRate c n)⁻¹ *
              (Real.log 3 + Real.log (n : ℝ) + r)) := by
        field_simp [hδne]
      _ ≤ scaledLinearSingletonRate c n * (k : ℝ) := hscaled
  have hthreshold : Real.log A + r ≤ δ * (k : ℝ) := by
    rw [hlogA]
    exact hthreshold0
  have hreal : A * (1 - δ) ^ k ≤ Real.exp (-r) :=
    geometricPrefactorPow_le_exp_neg_of_log_add_le hApos hδ1 k r hthreshold
  have hgeo :=
    wittMutation_firstHittingTime_tailMass_le_geometric_scaled_of_c3Envelope
      hn hc0 hp1 henv w hw hmono x hx k
  have hreal' :
      (3 * (n : ℝ)) *
          (1 - scaledLinearSingletonRate c n) ^ k ≤ Real.exp (-r) := by
    change A * (1 - δ) ^ k ≤ Real.exp (-r)
    exact hreal
  exact hgeo.trans (ENNReal.ofReal_le_ofReal hreal')

/-- Completely explicit shifted tail obtained from an arbitrary finite C3 envelope. -/
theorem wittMutation_firstHittingTime_tailMass_le_exp_shifted_of_c3Envelope
    {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 < c) (hp1 : scaledMutationRate c n < 1)
    (henv : WittMutationC3EnvelopeCondition (scaledMutationRate c n) n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (hr : 0 ≤ r) (k : ℕ)
    (hk : ((3 / c) * (n : ℝ)) *
        (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearScaledTrajectoryMeasureOfLtOne hc0.le hp1 w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hfactor : 0 ≤ Real.log 3 + Real.log (n : ℝ) + r := by linarith
  have hrate :=
    scaledLinearSingletonRate_inv_le_three_div_scale_mul_n_of_c3Envelope
      hn hc0 hp1 henv
  have hexact :
      (scaledLinearSingletonRate c n)⁻¹ *
          (Real.log 3 + Real.log (n : ℝ) + r) ≤ (k : ℝ) := by
    calc
      (scaledLinearSingletonRate c n)⁻¹ *
          (Real.log 3 + Real.log (n : ℝ) + r) ≤
        ((3 / c) * (n : ℝ)) *
          (Real.log 3 + Real.log (n : ℝ) + r) :=
        mul_le_mul_of_nonneg_right hrate hfactor
      _ ≤ (k : ℝ) := hk
  exact
    wittMutation_firstHittingTime_tailMass_le_exp_shifted_exactRate_of_c3Envelope
      hn hc0 hp1 henv w hw hmono x hx r k hexact

end ECRuntime
