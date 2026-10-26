import ECRuntime.GeometricFailureProductTailRecursion
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 70: recurrence for the canonical independent geometric sum

This module transports the split failure-product recurrence through the already
verified pushforward from failure vectors to `geometricWaitingSumMeasure`.
Thus the actual comparison law now satisfies the same final-coordinate
recurrence as the algebraic table from fix 69.
-/

/-- The zero-dimensional independent geometric sum is identically zero, hence
has zero strict tail at every natural threshold. -/
theorem geometricWaitingSumMeasure_fin_zero_tail
    (p : Fin 0 -> unitInterval) (k : Nat) :
    runtimeTailMass (geometricWaitingSumMeasure p) id (k : ENNReal) = 0 := by
  rw [← geometricFailureVectorWaitingSum_runtimeTailMass p (k : ENNReal)]
  unfold runtimeTailMass runtimeTailEvent
  have hevent :
      {failures : Fin 0 -> Nat |
        (k : ENNReal) < geometricFailureVectorWaitingSum failures} =
        (∅ : Set (Fin 0 -> Nat)) := by
    ext failures
    simp [geometricFailureVectorWaitingSum, geometricWaitingSum,
      geometricWaitingVectorOfFailureCounts]
  rw [hevent]
  simp

/-- Every nonempty geometric waiting sum is strictly positive, so its tail above
zero has probability one. -/
theorem geometricWaitingSumMeasure_positive_tail_zero
    {n : Nat} (p : Fin (n + 1) -> unitInterval) :
    runtimeTailMass (geometricWaitingSumMeasure p) id 0 = 1 := by
  rw [← geometricFailureVectorWaitingSum_runtimeTailMass p 0]
  unfold runtimeTailMass
  have hpositive : forall failures : Fin (n + 1) -> Nat,
      0 < geometricFailureVectorWaitingSum failures := by
    intro failures
    unfold geometricFailureVectorWaitingSum geometricWaitingSum
    unfold geometricWaitingVectorOfFailureCounts
    rw [Fin.sum_univ_castSucc]
    have hlast :
        0 < geometricWaitingTime (failures (Fin.last n)) := by
      simp [geometricWaitingTime]
    have hle0 :=
      add_le_add_right
        (show (0 : ENNReal) <=
          ∑ i : Fin n, geometricWaitingTime (failures i.castSucc) from bot_le)
        (geometricWaitingTime (failures (Fin.last n)))
    have hle :
        geometricWaitingTime (failures (Fin.last n)) <=
          (∑ i : Fin n, geometricWaitingTime (failures i.castSucc)) +
            geometricWaitingTime (failures (Fin.last n)) := by
      calc
        geometricWaitingTime (failures (Fin.last n)) =
            geometricWaitingTime (failures (Fin.last n)) + 0 := by simp
        _ <= geometricWaitingTime (failures (Fin.last n)) +
            (∑ i : Fin n, geometricWaitingTime (failures i.castSucc)) := hle0
        _ = (∑ i : Fin n, geometricWaitingTime (failures i.castSucc)) +
            geometricWaitingTime (failures (Fin.last n)) := add_comm _ _
    exact lt_of_lt_of_le hlast hle
  have hevent :
      runtimeTailEvent
          (geometricFailureVectorWaitingSum (m := n + 1)) 0 =
        Set.univ := by
    ext failures
    simp only [runtimeTailEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hpositive failures
  rw [hevent]
  exact measure_univ

/-- Final-coordinate recurrence for the natural-threshold tails of the
canonical independent geometric-sum law. -/
theorem geometricWaitingSumMeasure_tail_succ
    {n : Nat} (p : Fin (n + 1) -> unitInterval)
    (hp : forall i, Not (p i = 0)) (k : Nat) :
    runtimeTailMass
        (geometricWaitingSumMeasure p) id
        ((k + 1 : Nat) : ENNReal) =
      ENNReal.ofReal (1 - (p (Fin.last n) : Real)) *
        runtimeTailMass
          (geometricWaitingSumMeasure p) id (k : ENNReal) +
      ENNReal.ofReal (p (Fin.last n) : Real) *
        runtimeTailMass
          (geometricWaitingSumMeasure
            (fun i : Fin n => p i.castSucc)) id (k : ENNReal) := by
  rw [← geometricFailureVectorWaitingSum_runtimeTailMass p
    ((k + 1 : Nat) : ENNReal)]
  rw [geometricFailureProductMeasure_tail_splitLast p
    ((k + 1 : Nat) : ENNReal)]
  rw [geometricFailureSplitWaitingSum_tail_succ
    (p (Fin.last n)) (hp (Fin.last n))
    (fun i : Fin n => p i.castSucc) k]
  rw [← geometricFailureProductMeasure_tail_splitLast p (k : ENNReal)]
  rw [geometricFailureVectorWaitingSum_runtimeTailMass p (k : ENNReal)]
  rw [geometricFailureVectorWaitingSum_runtimeTailMass
    (fun i : Fin n => p i.castSucc) (k : ENNReal)]

end ECRuntime
