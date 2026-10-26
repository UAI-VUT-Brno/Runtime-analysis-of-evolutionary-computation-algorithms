import ECRuntime.GeometricFailureProductSplit
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 70: one-step tail recursion on the split failure product

Memorylessness is now lifted from one geometric failure coordinate to the
binary product consisting of the final coordinate and an arbitrary geometric
prefix.  The resulting recurrence is exactly the probabilistic recurrence used
by the algebraic table from fix 69.
-/

@[simp] theorem geometricWaitingTime_succ (r : Nat) :
    geometricWaitingTime (r + 1) = 1 + geometricWaitingTime r := by
  simp [geometricWaitingTime, Nat.cast_add, add_comm]

/-- On the zero-failure branch, crossing threshold `k+1` is equivalent to the
prefix sum crossing threshold `k`. -/
theorem geometricFailureSplitWaitingSum_zero_tail_preimage
    {n : Nat} (k : Nat) :
    Prod.mk 0 ⁻¹'
        runtimeTailEvent
          (geometricFailureSplitWaitingSum (n := n))
          ((k + 1 : Nat) : ENNReal) =
      runtimeTailEvent
        (geometricFailureVectorWaitingSum (m := n))
        (k : ENNReal) := by
  ext failures
  change
    ((k + 1 : Nat) : ENNReal) <
        geometricWaitingTime 0 + geometricFailureVectorWaitingSum failures ↔
      (k : ENNReal) < geometricFailureVectorWaitingSum failures
  rw [geometricWaitingTime_zero]
  simp [add_comm]

/-- On the positive-failure branch, removing the leading failure lowers both
sides of the strict threshold comparison by one. -/
theorem geometricFailureSplitWaitingSum_succ_tail_preimage
    {n : Nat} (k : Nat) :
    Prod.map Nat.succ id ⁻¹'
        runtimeTailEvent
          (geometricFailureSplitWaitingSum (n := n))
          ((k + 1 : Nat) : ENNReal) =
      runtimeTailEvent
        (geometricFailureSplitWaitingSum (n := n))
        (k : ENNReal) := by
  ext z
  change
    ((k + 1 : Nat) : ENNReal) <
        geometricWaitingTime (Nat.succ z.1) +
          geometricFailureVectorWaitingSum z.2 ↔
      (k : ENNReal) <
        geometricWaitingTime z.1 + geometricFailureVectorWaitingSum z.2
  rw [show Nat.succ z.1 = z.1 + 1 by omega]
  rw [geometricWaitingTime_succ]
  have h := ENNReal.add_lt_add_iff_left
    (a := (1 : ENNReal))
    (b := (k : ENNReal))
    (c := geometricWaitingTime z.1 +
      geometricFailureVectorWaitingSum z.2)
    ENNReal.one_ne_top
  simpa [add_assoc, add_comm, add_left_comm] using h

/-- The zero-failure product branch is exactly the prefix tail one threshold
lower. -/
theorem runtimeTailMass_diracZero_prod_geometricPrefix
    {n : Nat} (p : Fin n -> unitInterval) (k : Nat) :
    runtimeTailMass
        ((Measure.dirac 0).prod (geometricFailureProductMeasure p))
        geometricFailureSplitWaitingSum
        ((k + 1 : Nat) : ENNReal) =
      runtimeTailMass
        (geometricFailureProductMeasure p)
        geometricFailureVectorWaitingSum
        (k : ENNReal) := by
  unfold runtimeTailMass
  rw [Measure.dirac_prod 0]
  rw [Measure.map_apply measurable_prodMk_left
    (measurableSet_runtimeTailEvent
      measurable_geometricFailureSplitWaitingSum
      ((k + 1 : Nat) : ENNReal))]
  rw [geometricFailureSplitWaitingSum_zero_tail_preimage]

/-- Mapping successor on the final failure coordinate turns the threshold
`k+1` tail into the original split-product threshold `k` tail. -/
theorem runtimeTailMass_mapSucc_prod_geometricPrefix
    {n : Nat} (q : unitInterval) (p : Fin n -> unitInterval) (k : Nat) :
    runtimeTailMass
        (((geometricFailureMeasure q).map Nat.succ).prod
          (geometricFailureProductMeasure p))
        geometricFailureSplitWaitingSum
        ((k + 1 : Nat) : ENNReal) =
      runtimeTailMass
        ((geometricFailureMeasure q).prod
          (geometricFailureProductMeasure p))
        geometricFailureSplitWaitingSum
        (k : ENNReal) := by
  have hprod :
      ((geometricFailureMeasure q).map Nat.succ).prod
          (geometricFailureProductMeasure p) =
        ((geometricFailureMeasure q).prod
          (geometricFailureProductMeasure p)).map
            (Prod.map Nat.succ id) := by
    simpa using Measure.map_prod_map
      (geometricFailureMeasure q)
      (geometricFailureProductMeasure p)
      measurable_natSucc measurable_id
  rw [hprod]
  unfold runtimeTailMass
  rw [Measure.map_apply
    (measurable_natSucc.prodMap measurable_id)
    (measurableSet_runtimeTailEvent
      measurable_geometricFailureSplitWaitingSum
      ((k + 1 : Nat) : ENNReal))]
  rw [geometricFailureSplitWaitingSum_succ_tail_preimage]

/-- Exact one-step tail recursion for a final geometric failure coordinate plus
an independent geometric prefix. -/
theorem geometricFailureSplitWaitingSum_tail_succ
    {n : Nat} (q : unitInterval) (hq : Not (q = 0))
    (p : Fin n -> unitInterval) (k : Nat) :
    runtimeTailMass
        ((geometricFailureMeasure q).prod
          (geometricFailureProductMeasure p))
        geometricFailureSplitWaitingSum
        ((k + 1 : Nat) : ENNReal) =
      ENNReal.ofReal (1 - (q : Real)) *
        runtimeTailMass
          ((geometricFailureMeasure q).prod
            (geometricFailureProductMeasure p))
          geometricFailureSplitWaitingSum
          (k : ENNReal) +
      ENNReal.ofReal (q : Real) *
        runtimeTailMass
          (geometricFailureProductMeasure p)
          geometricFailureVectorWaitingSum
          (k : ENNReal) := by
  calc
    runtimeTailMass
        ((geometricFailureMeasure q).prod
          (geometricFailureProductMeasure p))
        geometricFailureSplitWaitingSum
        ((k + 1 : Nat) : ENNReal) =
      runtimeTailMass
        ((ENNReal.ofReal (q : Real) • Measure.dirac 0 +
            ENNReal.ofReal (1 - (q : Real)) •
              (geometricFailureMeasure q).map Nat.succ).prod
          (geometricFailureProductMeasure p))
        geometricFailureSplitWaitingSum
        ((k + 1 : Nat) : ENNReal) := by
      exact congrArg
        (fun mu : Measure Nat =>
          runtimeTailMass
            (mu.prod (geometricFailureProductMeasure p))
            geometricFailureSplitWaitingSum
            ((k + 1 : Nat) : ENNReal))
        (geometricFailureMeasure_memoryless hq)
    _ =
      ENNReal.ofReal (q : Real) *
          runtimeTailMass
            ((Measure.dirac 0).prod (geometricFailureProductMeasure p))
            geometricFailureSplitWaitingSum
            ((k + 1 : Nat) : ENNReal) +
        ENNReal.ofReal (1 - (q : Real)) *
          runtimeTailMass
            (((geometricFailureMeasure q).map Nat.succ).prod
              (geometricFailureProductMeasure p))
            geometricFailureSplitWaitingSum
            ((k + 1 : Nat) : ENNReal) := by
      rw [Measure.add_prod]
      rw [Measure.prod_smul_left, Measure.prod_smul_left]
      unfold runtimeTailMass
      rw [Measure.add_apply]
      simp only [Measure.smul_apply, smul_eq_mul]
    _ =
      ENNReal.ofReal (q : Real) *
          runtimeTailMass
            (geometricFailureProductMeasure p)
            geometricFailureVectorWaitingSum
            (k : ENNReal) +
        ENNReal.ofReal (1 - (q : Real)) *
          runtimeTailMass
            ((geometricFailureMeasure q).prod
              (geometricFailureProductMeasure p))
            geometricFailureSplitWaitingSum
            (k : ENNReal) := by
      rw [runtimeTailMass_diracZero_prod_geometricPrefix p k]
      rw [runtimeTailMass_mapSucc_prod_geometricPrefix q p k]
    _ =
      ENNReal.ofReal (1 - (q : Real)) *
          runtimeTailMass
            ((geometricFailureMeasure q).prod
              (geometricFailureProductMeasure p))
            geometricFailureSplitWaitingSum
            (k : ENNReal) +
        ENNReal.ofReal (q : Real) *
          runtimeTailMass
            (geometricFailureProductMeasure p)
            geometricFailureVectorWaitingSum
            (k : ENNReal) := by
      apply add_comm

end ECRuntime
