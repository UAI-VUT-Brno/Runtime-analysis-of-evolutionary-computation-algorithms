import ECRuntime.GeometricFailureMemoryless
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 70: split the last geometric failure coordinate

The finite product of failure-count laws is now split into its final coordinate
and the preceding prefix using Mathlib's measurable `Fin` product equivalence.
This is the product-space counterpart of the final-coordinate recursion in
`GeometricPrefixTailRecursion.lean`.
-/

/-- Measurable equivalence that exposes the final coordinate of a finite failure
vector and leaves the preceding coordinates in their natural order. -/
noncomputable def geometricFailureSplitLast (n : Nat) :
    (Fin (n + 1) -> Nat) ≃ᵐ Nat × (Fin n -> Nat) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Nat) (Fin.last n)

/-- The independent failure product splits exactly into the last geometric law
and the product of the preceding coordinates. -/
theorem geometricFailureProductMeasure_map_splitLast
    {n : Nat} (p : Fin (n + 1) -> unitInterval) :
    (geometricFailureProductMeasure p).map
        (geometricFailureSplitLast n) =
      (geometricFailureMeasure (p (Fin.last n))).prod
        (geometricFailureProductMeasure
          (fun i : Fin n => p i.castSucc)) := by
  have h := measurePreserving_piFinSuccAbove
    (fun i : Fin (n + 1) => geometricFailureMeasure (p i))
    (Fin.last n)
  simpa [geometricFailureProductMeasure, geometricFailureSplitLast,
    Fin.succAbove_last] using h.map_eq

/-- Waiting sum on the binary space obtained after exposing the final failure
coordinate. -/
noncomputable def geometricFailureSplitWaitingSum {n : Nat}
    (z : Nat × (Fin n -> Nat)) : ENNReal :=
  geometricWaitingTime z.1 + geometricFailureVectorWaitingSum z.2

/-- The split waiting sum is measurable. -/
theorem measurable_geometricFailureSplitWaitingSum {n : Nat} :
    Measurable (geometricFailureSplitWaitingSum (n := n)) := by
  unfold geometricFailureSplitWaitingSum
  exact (measurable_geometricWaitingTime.comp measurable_fst).add
    (measurable_geometricFailureVectorWaitingSum.comp measurable_snd)

/-- Pointwise, the waiting sum of the full vector is the waiting time of the
last coordinate plus the waiting sum of the prefix. -/
theorem geometricFailureVectorWaitingSum_splitLast
    {n : Nat} (failures : Fin (n + 1) -> Nat) :
    geometricFailureVectorWaitingSum failures =
      geometricFailureSplitWaitingSum
        (geometricFailureSplitLast n failures) := by
  classical
  unfold geometricFailureVectorWaitingSum geometricFailureSplitWaitingSum
  unfold geometricWaitingSum geometricWaitingVectorOfFailureCounts
  rw [Fin.sum_univ_castSucc]
  simp [geometricFailureVectorWaitingSum, geometricWaitingSum,
    geometricWaitingVectorOfFailureCounts, geometricFailureSplitLast, Fin.init, add_comm]

/-- Runtime tails of the full failure-vector waiting sum can be computed on the
binary last-coordinate/prefix product space. -/
theorem geometricFailureProductMeasure_tail_splitLast
    {n : Nat} (p : Fin (n + 1) -> unitInterval) (t : ENNReal) :
    runtimeTailMass
        (geometricFailureProductMeasure p)
        geometricFailureVectorWaitingSum t =
      runtimeTailMass
        ((geometricFailureMeasure (p (Fin.last n))).prod
          (geometricFailureProductMeasure
            (fun i : Fin n => p i.castSucc)))
        geometricFailureSplitWaitingSum t := by
  rw [← geometricFailureProductMeasure_map_splitLast p]
  unfold runtimeTailMass
  rw [Measure.map_apply
    (geometricFailureSplitLast n).measurable
    (measurableSet_runtimeTailEvent
      measurable_geometricFailureSplitWaitingSum t)]
  congr 1
  ext failures
  simp only [runtimeTailEvent, Set.mem_setOf_eq, Set.mem_preimage]
  rw [geometricFailureVectorWaitingSum_splitLast failures]

end ECRuntime
