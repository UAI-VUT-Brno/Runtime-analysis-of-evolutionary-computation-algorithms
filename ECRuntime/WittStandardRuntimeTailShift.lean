import ECRuntime.WittStandardRuntimeTail
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 41: shifted exponential tail for the sharp Witt runtime

Stage 40 proves the exact geometric natural-threshold estimate

`P(T > k) <= e n * (1 - 1/(e n))^k`.

This module performs only the elementary analytic conversion to the customary
shifted exponential tail.  The generic real inequality is isolated first: if
`A > 0`, `delta <= 1`, and

`log A + r <= delta * k`,

then

`A * (1 - delta)^k <= exp(-r)`.

For the refined Witt potential, `A = e n` and `delta = 1/(e n)`.  Since
`log(e n) = 1 + log n`, the natural-threshold hypothesis becomes

`e n * (1 + log n + r) <= k`.

No new drift, selection, or trajectory theorem is introduced here.
-/

/-- Elementary conversion of a geometric prefactor into a shifted exponential bound. -/
theorem geometricPrefactorPow_le_exp_neg_of_log_add_le
    {A δ : ℝ} (hA : 0 < A) (hδ1 : δ ≤ 1)
    (k : ℕ) (r : ℝ)
    (hk : Real.log A + r ≤ δ * (k : ℝ)) :
    A * (1 - δ) ^ k ≤ Real.exp (-r) := by
  have hq : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hbase : 1 - δ ≤ Real.exp (-δ) := Real.one_sub_le_exp_neg δ
  have hpow : (1 - δ) ^ k ≤ (Real.exp (-δ)) ^ k :=
    pow_le_pow_left₀ hq hbase k
  have hpowexp : (Real.exp (-δ)) ^ k = Real.exp (-(δ * (k : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    A * (1 - δ) ^ k ≤ A * (Real.exp (-δ)) ^ k :=
      mul_le_mul_of_nonneg_left hpow hA.le
    _ = Real.exp (Real.log A) * Real.exp (-(δ * (k : ℝ))) := by
      conv_lhs => rw [← Real.exp_log hA]
      rw [hpowexp]
    _ = Real.exp (Real.log A + (-(δ * (k : ℝ)))) := by
      rw [← Real.exp_add]
    _ = Real.exp (Real.log A - δ * (k : ℝ)) := by
      congr 1
    _ ≤ Real.exp (-r) := by
      rw [Real.exp_le_exp]
      linarith

/-- For positive dimension, `log(e n) = 1 + log n`. -/
theorem wittStandard_log_en
    {n : ℕ} (hn : 0 < n) :
    Real.log (Real.exp 1 * (n : ℝ)) = 1 + Real.log (n : ℝ) := by
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnrealne : (n : ℝ) ≠ 0 := ne_of_gt hnrealpos
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) hnrealne]
  simp

/-- Shifted exponential tail for the conventional optimization time of the standard-rate
`(1+1)` EA on positive nonincreasing linear objectives.

The threshold is kept as an explicit natural `k`, matching the repository's
`runtimeTailMass` interface. -/
theorem wittStandard_firstHittingTime_tailMass_le_exp_shifted
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ≠ allOnes n)
    (r : ℝ) (k : ℕ)
    (hk : (Real.exp 1 * (n : ℝ)) *
        (1 + Real.log (n : ℝ) + r) ≤ (k : ℝ)) :
    runtimeTailMass
        (linearStandardTrajectoryMeasure (by omega) w x)
        (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  let A : ℝ := Real.exp 1 * (n : ℝ)
  let δ : ℝ := wittStandardLinearDriftRate n
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos (Real.exp_pos 1) hnrealpos
  have hlogA : Real.log A = 1 + Real.log (n : ℝ) := by
    dsimp [A]
    exact wittStandard_log_en hnpos
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact wittStandardLinearDriftRate_le_one hn
  have hdiv : 1 + Real.log (n : ℝ) + r ≤ (k : ℝ) / A := by
    apply (le_div_iff₀ hApos).2
    change A * (1 + Real.log (n : ℝ) + r) ≤ (k : ℝ) at hk
    calc
      (1 + Real.log (n : ℝ) + r) * A =
          A * (1 + Real.log (n : ℝ) + r) := mul_comm _ _
      _ ≤ (k : ℝ) := hk
  have hδk : δ * (k : ℝ) = (k : ℝ) / A := by
    dsimp [δ, A]
    unfold wittStandardLinearDriftRate
    ring
  have hthreshold : Real.log A + r ≤ δ * (k : ℝ) := by
    rw [hlogA, hδk]
    exact hdiv
  have hreal : A * (1 - δ) ^ k ≤ Real.exp (-r) :=
    geometricPrefactorPow_le_exp_neg_of_log_add_le
      hApos hδ1 k r hthreshold
  have hgeo := wittStandard_firstHittingTime_tailMass_le_geometric
    hn w hw hmono x hx k
  have hreal' :
      (Real.exp 1 * (n : ℝ)) *
          (1 - wittStandardLinearDriftRate n) ^ k ≤ Real.exp (-r) := by
    change A * (1 - δ) ^ k ≤ Real.exp (-r)
    exact hreal
  exact hgeo.trans (ENNReal.ofReal_le_ofReal hreal')

end ECRuntime
