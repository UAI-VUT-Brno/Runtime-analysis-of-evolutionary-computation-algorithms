import ECRuntime.GeometricTail
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace ECRuntime

/--
Finite product law of one-based geometric waiting times with level-dependent
success probabilities `p i`.  A sample is a tuple of waiting times, one for
each level/index.
-/
noncomputable def geometricWaitingProductMeasure {m : ℕ}
    (p : Fin m → unitInterval) : Measure (Fin m → ENNReal) :=
  Measure.pi (fun i => geometricWaitingMeasure (p i))

instance instIsProbabilityMeasureGeometricWaitingProductMeasure
    {m : ℕ} (p : Fin m → unitInterval) :
    IsProbabilityMeasure (geometricWaitingProductMeasure p) := by
  unfold geometricWaitingProductMeasure
  infer_instance

/-- The `i`th waiting-time coordinate on the finite geometric product space. -/
def geometricWaitingCoordinate {m : ℕ} (i : Fin m) (ω : Fin m → ENNReal) : ENNReal :=
  ω i

/-- Every coordinate projection of the geometric product space is measurable. -/
theorem measurable_geometricWaitingCoordinate {m : ℕ} (i : Fin m) :
    Measurable (geometricWaitingCoordinate i) := by
  unfold geometricWaitingCoordinate
  exact measurable_pi_apply i

/--
The `i`th coordinate marginal of the geometric product law is exactly the
one-dimensional geometric waiting-time law with parameter `p i`.
-/
theorem geometricWaitingProductMeasure_map_coordinate
    {m : ℕ} (p : Fin m → unitInterval) (i : Fin m) :
    (geometricWaitingProductMeasure p).map (geometricWaitingCoordinate i) =
      geometricWaitingMeasure (p i) := by
  unfold geometricWaitingProductMeasure geometricWaitingCoordinate
  exact (measurePreserving_eval
    (fun j : Fin m => geometricWaitingMeasure (p j)) i).map_eq

/--
The waiting-time coordinates are mutually independent under their finite
product law.
-/
theorem iIndepFun_geometricWaitingCoordinate
    {m : ℕ} (p : Fin m → unitInterval) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin m => geometricWaitingCoordinate i)
      (geometricWaitingProductMeasure p) := by
  unfold geometricWaitingProductMeasure geometricWaitingCoordinate
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun i : Fin m => geometricWaitingMeasure (p i))
    (X := fun _ : Fin m => fun x : ENNReal => x)
    (fun _ => measurable_id.aemeasurable)

/--
Each coordinate has the exact geometric strict-tail profile on the joint
product space.
-/
theorem geometricWaitingProductMeasure_coordinate_tail_exact
    {m : ℕ} {p : Fin m → unitInterval} (i : Fin m)
    (hp : p i ≠ 0) (k : ℕ) :
    runtimeTailMass
        (geometricWaitingProductMeasure p)
        (geometricWaitingCoordinate i)
        (k : ENNReal) =
      geometricSurvival (p i) k := by
  unfold runtimeTailMass
  change geometricWaitingProductMeasure p
      ((geometricWaitingCoordinate i) ⁻¹' Set.Ioi (k : ENNReal)) =
    geometricSurvival (p i) k
  rw [← Measure.map_apply
      (measurable_geometricWaitingCoordinate i) measurableSet_Ioi]
  rw [geometricWaitingProductMeasure_map_coordinate p i]
  exact geometricWaitingMeasure_Ioi hp k

/-- Every coordinate satisfies the corresponding geometric tail certificate. -/
theorem hasGeometricTailBound_geometricWaitingCoordinate
    {m : ℕ} {p : Fin m → unitInterval} (i : Fin m)
    (hp : p i ≠ 0) :
    HasGeometricTailBound
      (geometricWaitingProductMeasure p)
      (geometricWaitingCoordinate i)
      (p i) := by
  intro k
  exact (geometricWaitingProductMeasure_coordinate_tail_exact i hp k).le

/-- The sum of all waiting-time coordinates in a finite geometric product. -/
noncomputable def geometricWaitingSum {m : ℕ} (ω : Fin m → ENNReal) : ENNReal :=
  ∑ i : Fin m, ω i

/-- A finite sum of geometric waiting-time coordinates is measurable. -/
theorem measurable_geometricWaitingSum {m : ℕ} :
    Measurable (geometricWaitingSum (m := m)) := by
  unfold geometricWaitingSum
  exact Finset.measurable_sum Finset.univ (by
    intro i _
    exact measurable_pi_apply i)

@[simp] theorem geometricWaitingSum_fin_zero (ω : Fin 0 → ENNReal) :
    geometricWaitingSum ω = 0 := by
  simp [geometricWaitingSum]

/--
The law of the finite sum of independent one-based geometric waiting times.
This is the canonical comparison law used by the distributional fitness-level
method.
-/
noncomputable def geometricWaitingSumMeasure {m : ℕ}
    (p : Fin m → unitInterval) : Measure ENNReal :=
  (geometricWaitingProductMeasure p).map geometricWaitingSum

instance instIsProbabilityMeasureGeometricWaitingSumMeasure
    {m : ℕ} (p : Fin m → unitInterval) :
    IsProbabilityMeasure (geometricWaitingSumMeasure p) := by
  unfold geometricWaitingSumMeasure
  exact Measure.isProbabilityMeasure_map
    measurable_geometricWaitingSum.aemeasurable

/--
Viewing the sum under the product space or the identity under its pushed-forward
law gives the same strict upper-tail mass.
-/
theorem geometricWaitingSumMeasure_runtimeTailMass
    {m : ℕ} (p : Fin m → unitInterval) (t : ENNReal) :
    runtimeTailMass (geometricWaitingSumMeasure p) id t =
      runtimeTailMass
        (geometricWaitingProductMeasure p) geometricWaitingSum t := by
  unfold runtimeTailMass runtimeTailEvent
  change geometricWaitingSumMeasure p (Set.Ioi t) =
    geometricWaitingProductMeasure p (geometricWaitingSum ⁻¹' Set.Ioi t)
  unfold geometricWaitingSumMeasure
  exact Measure.map_apply measurable_geometricWaitingSum measurableSet_Ioi

end ECRuntime
