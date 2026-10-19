import ECRuntime.MultiplicativeDriftTail
import ECRuntime.WittStandardRuntimeAsymptotics
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 40: geometric natural-threshold tail for the sharp Witt runtime

This module specializes the generic finite-state multiplicative-drift tail theorem to
the refined Witt potential already verified in Stages 30--39.  For every non-optimal
initial state and every natural threshold `k`, the conventional sample-path hitting
time obeys

`P(T > k) <= e n * (1 - 1/(e n))^k`.

The statement is deliberately kept in the exact geometric form supplied by the finite
survival recursion.  Converting this to the more customary shifted `exp(-r)` form is a
separate elementary analytic corollary and can be added after this compiler boundary is
stable.
-/

/-- The sharp Witt drift rate lies in `[0,1]` for the dimensions used by the theorem. -/
theorem wittStandardLinearDriftRate_le_one
    {n : ℕ} (hn : 4 ≤ n) :
    wittStandardLinearDriftRate n ≤ 1 := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hexp : (1 : ℝ) ≤ Real.exp 1 := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := (Real.exp_le_exp).2 (by norm_num)
  have hden : (1 : ℝ) ≤ Real.exp 1 * (n : ℝ) := by
    have hmul := mul_le_mul hexp hnreal (by norm_num : (0 : ℝ) ≤ 1)
      (Real.exp_pos 1).le
    simpa using hmul
  have hdenpos : 0 < Real.exp 1 * (n : ℝ) := by
    exact mul_pos (Real.exp_pos 1) (by exact_mod_cast (show 0 < n by omega))
  unfold wittStandardLinearDriftRate
  exact (div_le_one hdenpos).2 hden

/-- Natural-threshold geometric tail for the conventional optimization time of the
standard-rate `(1+1)` EA on every positive nonincreasing linear objective. -/
theorem wittStandard_firstHittingTime_tailMass_le_geometric
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n) (k : ℕ) :
    runtimeTailMass
        (linearStandardTrajectoryMeasure (by omega) w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal
        ((Real.exp 1 * (n : ℝ)) *
          (1 - wittStandardLinearDriftRate n) ^ k) := by
  have hnpos : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hp := standardMutationRate_mem_unitInterval_linear hn2
  let P := onePlusOneTransition (standardMutationRate n) (linearFitness w)
  let V := wittStandardLinearPotential w
  have hP : IsStochastic P := by
    dsimp [P]
    exact onePlusOneTransition_stochastic hp.1 hp.2 (linearFitness w)
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget V → (1 : ℝ) ≤ V z := by
    intro z hz
    dsimp [V]
    apply one_le_wittStandardLinearPotential_of_ne_allOnes w z
    intro hall
    apply hz
    change wittStandardLinearPotential w z = 0
    rw [hall]
    exact wittStandardLinearPotential_allOnes w
  have hxTarget : x ∉ realPotentialTarget V := by
    intro hxt
    have hx0 : V x = 0 := by
      simpa [realPotentialTarget] using hxt
    apply hx
    dsimp [V] at hx0
    exact (wittStandardLinearPotential_eq_zero_iff w x).mp hx0
  have hδ0 : 0 ≤ wittStandardLinearDriftRate n :=
    (wittStandardLinearDriftRate_pos hnpos).le
  have hδ1 : wittStandardLinearDriftRate n ≤ 1 :=
    wittStandardLinearDriftRate_le_one hn
  have htail := multiplicativeDrift_firstHittingTime_tailMass_le
    P hP V (wittStandardLinearDriftRate n) 1
    hδ0 hδ1 (by norm_num)
    hmin
    (by
      dsimp [P, V]
      exact wittStandard_hasMultiplicativeDriftLowerBound_sharp hn w hw hmono)
    x hxTarget k
  have htarget : realPotentialTarget V = oneMaxTarget n := by
    dsimp [V]
    exact wittStandardLinearTarget_eq_oneMaxTarget w
  have hhit :
      transitionTrajectoryFirstHittingTime (realPotentialTarget V) x =
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x :=
    transitionTrajectoryFirstHittingTime_congr_set
      (realPotentialTarget V) (oneMaxTarget n) htarget x
  have hVupper : V x ≤ Real.exp 1 * (n : ℝ) := by
    dsimp [V]
    calc
      wittStandardLinearPotential w x ≤ (n : ℝ) * Real.exp 1 :=
        wittStandardLinearPotential_le_en w x
      _ = Real.exp 1 * (n : ℝ) := by ring
  have hq : 0 ≤ 1 - wittStandardLinearDriftRate n :=
    sub_nonneg.mpr hδ1
  have hscale :
      (1 : ℝ)⁻¹ * V x * (1 - wittStandardLinearDriftRate n) ^ k ≤
        (Real.exp 1 * (n : ℝ)) *
          (1 - wittStandardLinearDriftRate n) ^ k := by
    norm_num
    exact mul_le_mul_of_nonneg_right hVupper (pow_nonneg hq k)
  unfold linearStandardTrajectoryMeasure
  rw [← hhit]
  exact htail.trans (ENNReal.ofReal_le_ofReal hscale)

end ECRuntime
