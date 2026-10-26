import ECRuntime.GenericFixedTargetAdditiveDriftLower
import ECRuntime.UnaryOneMaxExpectedProgressMeanRadius
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.OneMax
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-- The clipped zero-count potential is one-Lipschitz along an accepted
OneMax descent. This is the elementary part of the threshold drift bound;
the remaining obligation is to lift it through the unary mask kernel. -/
private theorem proof67_clippedZeroCount_decrease_le_raw
    (a b k : Nat) (hba : b ≤ a) :
    (((a - k : Nat) : Real) - ((b - k : Nat) : Real)) ≤
      ((a : Real) - (b : Real)) := by
  have hnat : a - k + b ≤ b - k + a := by omega
  have hreal :
      ((a - k : Nat) : Real) + (b : Real) ≤
        ((b - k : Nat) : Real) + (a : Real) := by
    exact_mod_cast hnat
  linarith

/-! P07: a nonoptimal fixed-target lower bound, rather than the special
case of hitting the all-ones vertex. The potential is the truncated
zero-count; progress is at most mean radius even across multi-bit leaps.
The truncation/clipping lemma is a real mathematical obligation. -/

/-- Starting at d > k zeros, reaching any point with at most k zeros
requires at least (d-k)/chi iterations in expectation. -/
theorem proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius
    {n : Nat} (hn : 0 < n) (k : Nat)
    (law : StaticUnaryUnbiasedMutation n) (hmean : 0 < law.meanRadius)
    (x : BitString n) (hx : k < zeroCount x) :
    ENNReal.ofReal (((zeroCount x - k : Nat) : Real) / law.meanRadius) ≤
      runtimeSup (law.transition (oneMaxReal (n := n)))
        ({y : BitString n | zeroCount y ≤ k} : Set (BitString n)) x := by
  classical
  let P : TransitionMatrix (BitString n) := law.transition oneMaxReal
  let target : Set (BitString n) := {y | zeroCount y ≤ k}
  let V : BitString n → Real :=
    fun y => ((zeroCount y - k : Nat) : Real)
  have hP : IsStochastic P := law.transition_stochastic _
  have hpot : ∀ y : BitString n, 0 ≤ V y := by
    intro y
    exact Nat.cast_nonneg _
  have hzero : ∀ y ∈ target, V y = 0 := by
    intro y hy
    change ((zeroCount y - k : Nat) : Real) = 0
    change zeroCount y ≤ k at hy
    simp [Nat.sub_eq_zero_of_le hy]
  have houtside : x ∉ target := by
    change ¬ zeroCount x ≤ k
    omega
  have hstep : ∀ y : BitString n, y ∉ target →
      (∑ z : BitString n, P y z * (V y - V z)) ≤
        law.meanRadius := by
    intro y _hy
    -- For any stochastic finite kernel, the expected pointwise change
    -- is exactly the drift of its potential.
    have hsum (W : BitString n → Real) :
        (∑ z : BitString n, P y z * (W y - W z)) =
          driftAt P W y := by
      calc
        (∑ z : BitString n, P y z * (W y - W z)) =
            (∑ z : BitString n, P y z) * W y -
              ∑ z : BitString n, P y z * W z := by
                rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro z _
                ring
        _ = driftAt P W y := by
              rw [hP.2 y, one_mul]
              rfl
    -- Elitist OneMax never increases the zero count. Clipping the
    -- potential at threshold k therefore cannot increase any accepted
    -- mask's potential decrease (an exact Nat.sub Lipschitz fact).
    have hclip :
        driftAt P V y ≤
          driftAt P (fun z : BitString n => (zeroCount z : Real)) y := by
      change
        driftAt (law.transition oneMaxReal) V y ≤
          driftAt (law.transition oneMaxReal)
            (fun z : BitString n => (zeroCount z : Real)) y
      rw [law.drift_eq_mask_sum oneMaxReal V y,
          law.drift_eq_mask_sum oneMaxReal
            (fun z : BitString n => (zeroCount z : Real)) y]
      apply Finset.sum_le_sum
      intro mask _
      have hm := oneMaxPotential_selectedAfterMask_le y mask
      change zeroCount (selectedAfterMask oneMaxReal y mask) ≤ zeroCount y at hm
      exact mul_le_mul_of_nonneg_left
        (show V y - V (selectedAfterMask oneMaxReal y mask) ≤
            (zeroCount y : Real) -
              (zeroCount (selectedAfterMask oneMaxReal y mask) : Real) from
          proof67_clippedZeroCount_decrease_le_raw
            (zeroCount y) (zeroCount (selectedAfterMask oneMaxReal y mask)) k hm)
        (law.weight_nonneg mask)
    have hraw :
        driftAt P (fun z : BitString n => (zeroCount z : Real)) y ≤
          (zeroCount y : Real) * (law.meanRadius / (n : Real)) := by
      rw [← hsum (fun z : BitString n => (zeroCount z : Real))]
      simpa only [P] using
        (proposed_unaryOneMax_expectedZeroDecrease_le_meanRadius hn law y)
    have hnreal : 0 < (n : Real) := by exact_mod_cast hn
    have hzeros : (zeroCount y : Real) ≤ (n : Real) := by
      exact_mod_cast zeroCount_le y
    have hfactor : (zeroCount y : Real) / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnreal).2 (by simpa using hzeros)
    have hbound :
        (zeroCount y : Real) * (law.meanRadius / (n : Real)) ≤
          law.meanRadius := by
      calc
        (zeroCount y : Real) * (law.meanRadius / (n : Real)) =
            ((zeroCount y : Real) / (n : Real)) * law.meanRadius := by ring
        _ ≤ 1 * law.meanRadius :=
          mul_le_mul_of_nonneg_right hfactor hmean.le
        _ = law.meanRadius := one_mul _
    rw [hsum V]
    exact hclip.trans (hraw.trans hbound)
  convert (proposed_genericFixedTarget_additiveDrift_runtimeLower
    P hP target V hpot hzero law.meanRadius hmean hstep x houtside)
    using 1
  exact @runtimeSup_congr_target (BitString n) inferInstance
    P target target
    (fun y => Set.decidableSetOf y (fun z : BitString n => zeroCount z ≤ k))
    (fun y => Classical.propDecidable (y ∈ target)) rfl x

end ECRuntime
