import ECRuntime.WittStandardStrictTailDownset
import ECRuntime.ExpectedRuntimeCorollaries
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 38: sharp standard-rate runtime endpoint for positive linear functions

Stage 37 fix 2 closes the finite-dimensional one-step part of Witt's sharp
standard-rate argument: for every positive nonincreasing linear objective and
`n >= 4`, the refined Witt potential has multiplicative drift at least
`1 / (e n)`.

This module performs only the deterministic/runtime assembly.  The refined
potential is zero exactly at the all-ones optimum, every nonzero value is at
least one, and every value is at most `e n`.  The generic multiplicative-drift
runtime theorem therefore gives the finite-dimensional bound

`e n * (2 + log n)`.

The same bound is then transported through the already-verified
`runtimeSup = integral(first hitting time)` bridge to the conventional
sample-path expected optimization time.  Exponential-tail consequences are
left to a later module, because the repository does not yet contain a generic
multiplicative-drift tail theorem.
-/

/-- The zero level of the refined Witt potential is the canonical all-ones target. -/
theorem wittStandardLinearTarget_eq_oneMaxTarget {n : ℕ}
    (w : Fin n → ℝ) :
    realPotentialTarget (wittStandardLinearPotential w) = oneMaxTarget n := by
  rw [oneMaxTarget_eq_singleton]
  ext x
  simp [realPotentialTarget, wittStandardLinearPotential_eq_zero_iff]

/-- The sharp one-step theorem plugged directly into the generic multiplicative-drift
runtime certificate. -/
theorem wittStandard_runtimeSup_le_certificate
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          (wittStandardLinearDriftRate n) 1
          (wittStandardLinearPotential w) x) := by
  have hnpos : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hp := standardMutationRate_mem_unitInterval_linear hn2
  have hP : IsStochastic
      (onePlusOneTransition (standardMutationRate n) (linearFitness w)) :=
    onePlusOneTransition_stochastic hp.1 hp.2 (linearFitness w)
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget (wittStandardLinearPotential w) →
        (1 : ℝ) ≤ wittStandardLinearPotential w z := by
    intro z hz
    apply one_le_wittStandardLinearPotential_of_ne_allOnes w z
    intro hall
    apply hz
    change wittStandardLinearPotential w z = 0
    rw [hall]
    exact wittStandardLinearPotential_allOnes w
  have hbound := multiplicativeDrift_runtimeSup_le
    (onePlusOneTransition (standardMutationRate n) (linearFitness w))
    (wittStandardLinearPotential w)
    (wittStandardLinearDriftRate n) 1
    hP (wittStandardLinearDriftRate_pos hnpos) (by norm_num)
    (wittStandardLinearPotential_nonneg w) hmin
    (wittStandard_hasMultiplicativeDriftLowerBound_sharp hn w hw hmono) x
  calc
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x =
      runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (realPotentialTarget (wittStandardLinearPotential w)) x := by
          symm
          exact runtimeSup_congr_target
            (onePlusOneTransition (standardMutationRate n) (linearFitness w))
            (realPotentialTarget (wittStandardLinearPotential w))
            (oneMaxTarget n)
            (wittStandardLinearTarget_eq_oneMaxTarget w) x
    _ ≤ ENNReal.ofReal
        (multiplicativeDriftRuntime
          (wittStandardLinearDriftRate n) 1
          (wittStandardLinearPotential w) x) := hbound

/-- The sharp Witt multiplicative-drift certificate is uniformly at most
`e n (2 + log n)`. -/
theorem wittStandard_multiplicativeRuntime_le_log_bound
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (x : BitString n) :
    multiplicativeDriftRuntime
        (wittStandardLinearDriftRate n) 1
        (wittStandardLinearPotential w) x ≤
      (Real.exp 1 * (n : ℝ)) * (2 + Real.log (n : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnrealne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  let V := wittStandardLinearPotential w
  let C : ℝ := Real.exp 1 * (n : ℝ)
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (Real.exp_pos 1) hnrealpos
  have hlogC : Real.log C = 1 + Real.log (n : ℝ) := by
    dsimp [C]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) hnrealne]
    simp
  change multiplicativeDriftRuntime
      (wittStandardLinearDriftRate n) 1 V x ≤
    C * (2 + Real.log (n : ℝ))
  by_cases hx0 : V x = 0
  · have hcert : multiplicativeDriftRuntime
        (wittStandardLinearDriftRate n) 1 V x = 0 := by
      unfold multiplicativeDriftRuntime additiveDriftRuntime
      simp [multiplicativeDriftPotential, hx0]
    rw [hcert]
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
    exact mul_nonneg hCpos.le (by linarith)
  · have hxpos : 0 < V x := by
      have hnonneg : 0 ≤ V x := by
        dsimp [V]
        exact wittStandardLinearPotential_nonneg w x
      exact lt_of_le_of_ne hnonneg (Ne.symm hx0)
    have hVupper : V x ≤ C := by
      dsimp [V, C]
      have h := wittStandardLinearPotential_le_en w x
      nlinarith
    have hlog : Real.log (V x) ≤ Real.log C :=
      Real.log_le_log hxpos hVupper
    have hcert : multiplicativeDriftRuntime
        (wittStandardLinearDriftRate n) 1 V x =
          C * (1 + Real.log (V x)) := by
      have hraw := multiplicativeDriftRuntime_eq_log_ratio
        V (wittStandardLinearDriftRate n) 1 (by norm_num) x hx0
      rw [hraw]
      dsimp [C]
      simp [wittStandardLinearDriftRate]
    rw [hcert]
    rw [hlogC] at hlog
    exact mul_le_mul_of_nonneg_left (by linarith) hCpos.le

/-- Sharp coefficient-independent finite-dimensional runtime bound for every positive
nonincreasing linear objective at the standard mutation rate. -/
theorem wittStandard_runtimeSup_le_log_bound
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        ((Real.exp 1 * (n : ℝ)) * (2 + Real.log (n : ℝ))) := by
  exact (wittStandard_runtimeSup_le_certificate hn w hw hmono x).trans
    (ENNReal.ofReal_le_ofReal
      (wittStandard_multiplicativeRuntime_le_log_bound hn w x))

/-- In particular, the sharp standard-rate linear runtime supremum is finite. -/
theorem wittStandard_runtimeSup_ne_top
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≠ ⊤ := by
  have hle := wittStandard_runtimeSup_le_log_bound hn w hw hmono x
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- Conventional sample-path expected first-hitting time satisfies the same sharp
finite-dimensional `e n (2 + log n)` bound. -/
theorem wittStandard_firstHittingTime_lintegral_le_log_bound
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂linearStandardTrajectoryMeasure (by omega) w x) ≤
      ENNReal.ofReal
        ((Real.exp 1 * (n : ℝ)) * (2 + Real.log (n : ℝ))) := by
  unfold linearStandardTrajectoryMeasure
  rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup]
  exact wittStandard_runtimeSup_le_log_bound hn w hw hmono x

/-- The conventional sharp standard-rate first-hitting time therefore has finite
expectation. -/
theorem wittStandard_firstHittingTime_lintegral_ne_top
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂linearStandardTrajectoryMeasure (by omega) w x) ≠ ⊤ := by
  have hle := wittStandard_firstHittingTime_lintegral_le_log_bound
    hn w hw hmono x
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end ECRuntime
