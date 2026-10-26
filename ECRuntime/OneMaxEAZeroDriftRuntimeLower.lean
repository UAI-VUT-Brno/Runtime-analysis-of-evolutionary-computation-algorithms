import ECRuntime.OneMaxEABoundedExpectedProgress
import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import ECRuntime.AdditiveDrift
import ECRuntime.GenericFixedTargetAdditiveDriftLower
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: targeted additive-drift lower bound for OneMax from the proposed
one-step progress upper bound and the general lower-drift result (Stage352).
This would be a genuine expected optimization-time statement, distinct
from geometric no-flip self-loop lower bounds. -/

/-- Expected time to reach the OneMax optimum is at least the initial
zero count divided by the maximal n*p expected progress per iteration. -/
theorem proposed_oneMaxEA_zeroCount_runtimeSup_ge_zeroCount_div_np
    {n : Nat} (hn : 0 < n) (p : Real) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x : BitString n) (hx : x ≠ allOnes n) :
    ENNReal.ofReal ((zeroCount x : Real) / ((n : Real) * p)) ≤
      runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
        ({allOnes n} : Set (BitString n)) x := by
  classical
  have hP : IsStochastic
      (onePlusOneTransition p (oneMaxReal (n := n))) :=
    onePlusOneTransition_stochastic hp0.le hp1 oneMaxReal
  have hd : 0 < (n : Real) * p :=
    mul_pos (by exact_mod_cast hn) hp0
  have hstep : ∀ y : BitString n,
      y ∉ ({allOnes n} : Set (BitString n)) →
        (∑ z : BitString n,
          onePlusOneTransition p oneMaxReal y z *
            ((zeroCount y : Real) - (zeroCount z : Real))) ≤
          (n : Real) * p := by
    intro y _hy
    have hm := proposed_oneMaxEA_expectedZeroDecrease_le_zeroCount_mul_p
      p hp0.le hp1 y
    have hz : (zeroCount y : Real) ≤ (n : Real) := by
      exact_mod_cast zeroCount_le y
    exact hm.trans (mul_le_mul_of_nonneg_right hz hp0.le)
  -- The singleton target may infer `Set.decidableSingleton` here, whereas
  -- the generic theorem used classical membership decidability. Avoid a
  -- dependent-type conversion failure via the certified congruence lemma.
  convert (proposed_genericFixedTarget_additiveDrift_runtimeLower
    (onePlusOneTransition p oneMaxReal) hP
    ({allOnes n} : Set (BitString n))
    (fun y => (zeroCount y : Real))
    (fun y => Nat.cast_nonneg (zeroCount y))
    (by intro y hy
        have hy' : y = allOnes n := Set.mem_singleton_iff.mp hy
        simp [hy'])
    ((n : Real) * p) hd hstep x (by simpa using hx)) using 1
  exact @runtimeSup_congr_target (BitString n) inferInstance
    (onePlusOneTransition p oneMaxReal)
    ({allOnes n} : Set (BitString n))
    ({allOnes n} : Set (BitString n))
    (fun a => Set.decidableSingleton a (allOnes n))
    (fun y => Classical.propDecidable (y ∈ ({allOnes n} : Set (BitString n))))
    rfl x

end ECRuntime
