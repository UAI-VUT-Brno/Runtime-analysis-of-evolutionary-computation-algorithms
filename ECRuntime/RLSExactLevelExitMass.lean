import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-! Stage 128: provisional public theorem; approved candidate proof compiled clean.
Source context: exact coupon collector / RLS fitness-level process.
This isolates the level-exit probability needed by the exact RLS hitting-time
and residence-time proof, without assuming independence of successive levels.
The statement was approved by the user in the Round 10 follow-up. -/

/-- When RLS on OneMax has `k>0` remaining zero bits, the exact one-step
probability of decreasing that number by one is `k/n`. -/
theorem proposed_rlsOneMax_exactLevelExitMass
    {n : Nat} (hn : 0 < n) (x : BitString n)
    (hk : 0 < zeroCount x) :
    finiteEventMass
      (((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal) x)
      (fun y : BitString n => zeroCount y = zeroCount x - 1) =
      (zeroCount x : Real) / (n : Real) := by
  classical
  let P := (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal
  let event : BitString n → Prop :=
    fun y => zeroCount y = zeroCount x - 1
  have hevent :
      finiteEventMass (P x) event =
        expectedValueAfter P (fun y => if event y then (1 : Real) else 0) x := by
    unfold finiteEventMass expectedValueAfter
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : event y
    · rw [Set.indicator_of_mem (show y ∈ ({z | event z} : Set (BitString n)) from hy) (P x)]
      simp [hy]
    · rw [Set.indicator_of_notMem (show y ∉ ({z | event z} : Set (BitString n)) from hy) (P x)]
      simp [hy]
  have hstep (i : Fin n) :
      (if event (selectedAfterMask oneMaxReal x ({i} : MutationMask n))
        then (1 : Real) else 0) =
      (if x i = false then 1 else 0) := by
    unfold event
    rw [candidate_rls_selectedZeroCount]
    by_cases hi : x i = false
    · simp [hi]
    · have hneq : zeroCount x ≠ zeroCount x - 1 := by omega
      simp [hi, hneq]
  have hsum :
      (∑ i : Fin n,
        if event (selectedAfterMask oneMaxReal x ({i} : MutationMask n))
          then (1 : Real) else 0) = (zeroCount x : Real) := by
    calc
      _ = ∑ i : Fin n, if x i = false then (1 : Real) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hstep i
      _ = _ := candidate_rls_sum_zeroIndicators x
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    finiteEventMass (P x) event =
        expectedValueAfter P (fun y => if event y then (1 : Real) else 0) x :=
          hevent
    _ = (n : Real)⁻¹ *
        (∑ i : Fin n,
          if event (selectedAfterMask oneMaxReal x ({i} : MutationMask n))
            then (1 : Real) else 0) := by
          exact candidate_rls_expectedValueAfter_eq_singleton_average hn
            oneMaxReal (fun y => if event y then (1 : Real) else 0) x
    _ = (n : Real)⁻¹ * (zeroCount x : Real) := by rw [hsum]
    _ = (zeroCount x : Real) / (n : Real) := by ring

end ECRuntime
