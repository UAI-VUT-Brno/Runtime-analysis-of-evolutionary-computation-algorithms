import ECRuntime.MultiplicativeDrift
import ECRuntime.LevelExitTrajectory
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-!
# Stage 40: natural-threshold tails from multiplicative drift

The expectation theorem in `MultiplicativeDrift.lean` is based on a logarithmic
Bellman supersolution.  For tail probabilities a more direct argument is available.
Let `V` be nonnegative, let positive states satisfy `V >= vmin > 0`, and suppose

`delta * V x <= V x - E[V(X_{t+1}) | X_t = x]`

away from the zero-potential target.  If `0 <= delta <= 1`, then the finite survival
recursion outside that target satisfies

`survival(k,x) <= vmin⁻¹ * V x * (1-delta)^k`.

The proof is a finite-state induction using the already verified
`finiteLevelSurvival` recursion.  It does not require the target to be absorbing:
paths are killed by the survival recursion as soon as the zero-potential target is
entered.

The second theorem transports this finite recursion to the conventional infinite-path
first-hitting time at every natural threshold through the Stage-26/25 trajectory
bridge.
-/

/-- Multiplicative drift gives geometric decay of the finite survival probability
outside the zero-potential target. -/
theorem finiteLevelSurvival_le_multiplicativeDrift
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℝ) (δ vmin : ℝ)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hvmin : 0 < vmin)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (hmult : HasMultiplicativeDriftLowerBound P V δ) :
    ∀ k x, x ∉ realPotentialTarget V →
      finiteLevelSurvival P ((realPotentialTarget V)ᶜ) k x ≤
        vmin⁻¹ * V x * (1 - δ) ^ k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hxLevel : x ∈ (realPotentialTarget V)ᶜ := hx
      rw [finiteLevelSurvival_zero_of_mem
        P ((realPotentialTarget V)ᶜ) x hxLevel]
      have hinvnonneg : 0 ≤ vmin⁻¹ := inv_nonneg.mpr hvmin.le
      have hscaled := mul_le_mul_of_nonneg_left (hmin x hx) hinvnonneg
      have hvminne : vmin ≠ 0 := ne_of_gt hvmin
      calc
        (1 : ℝ) = vmin⁻¹ * vmin := by
          rw [inv_mul_cancel₀ hvminne]
        _ ≤ vmin⁻¹ * V x := hscaled
        _ = vmin⁻¹ * V x * (1 - δ) ^ 0 := by simp
  | succ k ih =>
      intro x hx
      have hxLevel : x ∈ (realPotentialTarget V)ᶜ := hx
      rw [finiteLevelSurvival_succ_of_mem
        P ((realPotentialTarget V)ᶜ) k x hxLevel]
      have hq : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
      have hqpow : 0 ≤ (1 - δ) ^ k := pow_nonneg hq k
      have hxpos : 0 < V x := lt_of_lt_of_le hvmin (hmin x hx)
      have hmultx := hmult x hxpos
      have hEV : expectedValueAfter P V x ≤ (1 - δ) * V x := by
        unfold driftAt at hmultx
        linarith
      calc
        (∑ y, P x y *
            finiteLevelSurvival P ((realPotentialTarget V)ᶜ) k y) ≤
            ∑ y, P x y * (vmin⁻¹ * V y * (1 - δ) ^ k) := by
          apply Finset.sum_le_sum
          intro y _hy
          by_cases hy : y ∈ realPotentialTarget V
          · have hyNotLevel : y ∉ (realPotentialTarget V)ᶜ := by
              simpa using hy
            rw [finiteLevelSurvival_eq_zero_of_not_mem
              P ((realPotentialTarget V)ᶜ) k y hyNotLevel]
            have hy0 : V y = 0 := by
              simpa [realPotentialTarget] using hy
            simp [hy0]
          · exact mul_le_mul_of_nonneg_left (ih y hy) (hP.1 x y)
        _ = vmin⁻¹ * expectedValueAfter P V x * (1 - δ) ^ k := by
          unfold expectedValueAfter
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _hy
          ring
        _ ≤ vmin⁻¹ * ((1 - δ) * V x) * (1 - δ) ^ k := by
          have hscaled := mul_le_mul_of_nonneg_left hEV (inv_nonneg.mpr hvmin.le)
          exact mul_le_mul_of_nonneg_right hscaled hqpow
        _ = vmin⁻¹ * V x * (1 - δ) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Extensionality of the conventional first-hitting-time observable with respect to
its target set, including the `DecidablePred` argument carried by the definition. -/
theorem transitionTrajectoryFirstHittingTime_congr_set
    {α : Type*}
    (s t : Set α)
    [hs : DecidablePred (fun z => z ∈ s)]
    [ht : DecidablePred (fun z => z ∈ t)]
    (hst : s = t) (x : α) :
    transitionTrajectoryFirstHittingTime s x =
      transitionTrajectoryFirstHittingTime t x := by
  subst t
  have hdec : hs = ht := by
    funext z
    exact Subsingleton.elim (hs z) (ht z)
  cases hdec
  rfl

/-- Natural-threshold tail bound for the conventional first-hitting time obtained
from multiplicative drift. -/
theorem multiplicativeDrift_firstHittingTime_tailMass_le
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℝ) (δ vmin : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hvmin : 0 < vmin)
    (hmin : ∀ z, z ∉ realPotentialTarget V → vmin ≤ V z)
    (hmult : HasMultiplicativeDriftLowerBound P V δ)
    (x : α) (hx : x ∉ realPotentialTarget V) (k : ℕ) :
    runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (realPotentialTarget V) x)
        (k : ENNReal) ≤
      ENNReal.ofReal (vmin⁻¹ * V x * (1 - δ) ^ k) := by
  classical
  let level : Set α := (realPotentialTarget V)ᶜ
  have htarget : levelᶜ = realPotentialTarget V := by
    ext z
    simp [level]
  have hhit :
      transitionTrajectoryFirstHittingTime levelᶜ x =
        transitionTrajectoryFirstHittingTime (realPotentialTarget V) x :=
    transitionTrajectoryFirstHittingTime_congr_set
      levelᶜ (realPotentialTarget V) htarget x
  rw [← hhit]
  rw [transitionTrajectoryLevelExit_tailMass_eq_finiteLevelSurvival
    P level hP x k]
  exact ENNReal.ofReal_le_ofReal (by
    simpa [level] using
      finiteLevelSurvival_le_multiplicativeDrift
        P hP V δ vmin hδ0 hδ1 hvmin hmin hmult k x hx)

end ECRuntime
