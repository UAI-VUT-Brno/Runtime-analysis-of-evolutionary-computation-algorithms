import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.LinearRuntime
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-!
# Stage 25: sample-path expected-runtime corollaries

The Bellman `runtimeSup` bounds for OneMax and arbitrary positive nonincreasing linear
functions were proved much earlier in the development.  Stage 25 identifies
`runtimeSup` with the expectation of the conventional least-index first-hitting time.
This file records the resulting probability-theoretic endpoint theorems for the two
main EC applications.
-/

/-- Infinite trajectory law of the standard-rate `(1+1)` EA on OneMax. -/
noncomputable def oneMaxStandardTrajectoryMeasure
    {n : ℕ} (hn : 2 ≤ n)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) : Measure (ℕ → BitString n) :=
  transitionTrajectoryMeasure
    (onePlusOneTransition (standardMutationRate n) oneMaxReal)
    (onePlusOneTransition_stochastic
      (standardMutationRate_mem_unitInterval_linear hn).1
      (standardMutationRate_mem_unitInterval_linear hn).2
      oneMaxReal)
    x

/-- The actual sample-path expected first-hitting time of the standard-rate `(1+1)` EA
on OneMax satisfies the classical `e n H_n` bound. -/
theorem oneMax_standard_firstHittingTime_lintegral_le_classical
    {n : ℕ} (hn : 2 ≤ n)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂oneMaxStandardTrajectoryMeasure hn x) ≤
      ENNReal.ofReal (oneMaxClassicalRuntimeBound n) := by
  unfold oneMaxStandardTrajectoryMeasure
  rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup]
  exact oneMax_standard_runtimeSup_le_classical hn x

/-- The actual sample-path expected first-hitting time of the standard-rate `(1+1)` EA
on OneMax is at most `e n (1 + log n)`. -/
theorem oneMax_standard_firstHittingTime_lintegral_le_log
    {n : ℕ} (hn : 2 ≤ n)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂oneMaxStandardTrajectoryMeasure hn x) ≤
      ENNReal.ofReal
        (Real.exp 1 * (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  unfold oneMaxStandardTrajectoryMeasure
  rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup]
  exact oneMax_standard_runtimeSup_le_log hn x

/-- In particular, the standard-rate OneMax first-hitting time has finite expectation. -/
theorem oneMax_standard_firstHittingTime_lintegral_ne_top
    {n : ℕ} (hn : 2 ≤ n)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂oneMaxStandardTrajectoryMeasure hn x) ≠ ⊤ := by
  unfold oneMaxStandardTrajectoryMeasure
  rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup]
  exact oneMax_standard_runtimeSup_ne_top hn x

/-- Infinite trajectory law of the standard-rate `(1+1)` EA on an arbitrary linear
objective. -/
noncomputable def linearStandardTrajectoryMeasure
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) : Measure (ℕ → BitString n) :=
  transitionTrajectoryMeasure
    (onePlusOneTransition (standardMutationRate n) (linearFitness w))
    (onePlusOneTransition_stochastic
      (standardMutationRate_mem_unitInterval_linear hn).1
      (standardMutationRate_mem_unitInterval_linear hn).2
      (linearFitness w))
    x

/-- Main arbitrary-positive-linear sample-path theorem: for positive nonincreasing
coefficients, the expected first hitting time of the all-ones optimum is bounded by
`4 e n (1 + log(2n))`, independently of the coefficient magnitudes. -/
theorem linear_standard_firstHittingTime_lintegral_le_log_bound
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂linearStandardTrajectoryMeasure hn w x) ≤
      ENNReal.ofReal
        ((4 * Real.exp 1 * (n : ℝ)) *
          (1 + Real.log (2 * (n : ℝ)))) := by
  unfold linearStandardTrajectoryMeasure
  rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup]
  exact linear_runtimeSup_allOnes_le_log_bound hn w hw hmono x

/-- The first-hitting time of the standard-rate `(1+1)` EA on every positive
nonincreasing linear objective has finite expectation. -/
theorem linear_standard_firstHittingTime_lintegral_ne_top
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂linearStandardTrajectoryMeasure hn w x) ≠ ⊤ := by
  unfold linearStandardTrajectoryMeasure
  rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup]
  exact linear_runtimeSup_allOnes_ne_top hn w hw hmono x

end ECRuntime
