import ECRuntime.AdaptiveLeadingOnesUniformFullRuntime
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-!
P01 / Stage 245 completion bridge. This module is *independent* of frozen
Stage 245 (which remains byte-identical): the trajectory integral and the
certified Bellman runtime are identified by the existing Markov trajectory
integral theorem; the uniform runtime is Stage 392. No extra stopping-time
independence or assumed occupation identity is introduced.
-/

/-- Uniform-initial genuine pathwise hitting time has the full adaptive
LeadingOnes half-exit-sum mean. The conclusion is exactly the frozen
Stage-245 mathematical claim, stated without importing its admitted file. -/
theorem proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        ∫⁻ path : Nat → BitString n,
          transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
          ∂transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x) =
      ENNReal.ofReal ((1 / 2 : Real) *
        ∑ i : Fin n, (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  have hpath :
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          ∫⁻ path : Nat → BitString n,
            transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
            ∂transitionTrajectoryMeasure
              (leadingOnesAdaptiveTransition rate)
              (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          runtimeSup (leadingOnesAdaptiveTransition rate)
            (leadingOnesTarget n) x) := by
    congr 1
    apply Finset.sum_congr rfl
    intro x _hx
    exact transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
      (leadingOnesAdaptiveTransition rate) (leadingOnesTarget n)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
  rw [hpath, proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum
    n rate hinterior]
  have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : Real) := by
    simpa only [one_div] using ENNReal_ofReal_half.symm
  calc
    (∑ i : Fin n, (1 / 2 : ENNReal) *
      ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹)) =
      ∑ i : Fin n, ENNReal.ofReal
        ((1 / 2 : Real) *
          (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 1 / 2)]
    _ = ENNReal.ofReal (∑ i : Fin n, (1 / 2 : Real) *
      (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro i _hi
        have hp := hinterior i.val (Nat.le_of_lt i.isLt)
        have hbase : 0 ≤ rate i.val * (1 - rate i.val) ^ i.val :=
          mul_nonneg hp.1.le (pow_nonneg (by linarith [hp.2]) _)
        exact mul_nonneg (by norm_num) (inv_nonneg.mpr hbase)
    _ = ENNReal.ofReal ((1 / 2 : Real) *
      ∑ i : Fin n, (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
        rw [Finset.mul_sum]

end ECRuntime
