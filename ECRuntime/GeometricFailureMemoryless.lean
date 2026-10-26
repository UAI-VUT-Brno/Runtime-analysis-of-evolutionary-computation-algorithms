import ECRuntime.GeometricFailureCouplingReduction
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 70: geometric failure-law memorylessness

The direct Stage-26 route only needs a recurrence for the tail of the canonical
independent geometric sum.  The discrete failure-count representation from fix
52 makes the one-dimensional recurrence especially transparent: a geometric
failure count is zero with probability `p`, and otherwise is one plus a fresh
copy with weight `1-p`.
-/

/-- Natural-number successor is measurable on the discrete measurable space. -/
theorem measurable_natSucc : Measurable Nat.succ := by
  exact measurable_of_countable Nat.succ

/-- Exact measure decomposition expressing memorylessness of the geometric
failure-count law. -/
theorem geometricFailureMeasure_memoryless
    {p : unitInterval} (hp : Not (p = 0)) :
    geometricFailureMeasure p =
      ENNReal.ofReal (p : Real) • Measure.dirac 0 +
        ENNReal.ofReal (1 - (p : Real)) •
          (geometricFailureMeasure p).map Nat.succ := by
  apply (Measure.ext_iff_singleton).2
  intro n
  cases n with
  | zero =>
      have hpre : Nat.succ ⁻¹' ({0} : Set Nat) = (∅ : Set Nat) := by
        ext r
        simp
      rw [geometricFailureMeasure_singleton hp 0]
      rw [Measure.add_apply]
      simp only [Measure.smul_apply]
      rw [Measure.map_apply measurable_natSucc (MeasurableSet.singleton 0)]
      rw [hpre]
      simp
  | succ n =>
      have hpre : Nat.succ ⁻¹' ({n + 1} : Set Nat) = ({n} : Set Nat) := by
        ext r
        simp
      have hq : 0 <= 1 - (p : Real) := sub_nonneg.mpr p.property.2
      have hreal :
          (1 - (p : Real)) ^ (n + 1) * (p : Real) =
            (1 - (p : Real)) *
              ((1 - (p : Real)) ^ n * (p : Real)) := by
        ring
      rw [geometricFailureMeasure_singleton hp (n + 1)]
      rw [Measure.add_apply]
      simp only [Measure.smul_apply]
      rw [Measure.map_apply measurable_natSucc (MeasurableSet.singleton (n + 1))]
      rw [hpre, geometricFailureMeasure_singleton hp n]
      simp [hreal, ENNReal.ofReal_mul hq]

/-- The survival coefficient for one failure is exactly `ofReal (1-p)`. -/
theorem geometricSurvival_one
    (p : unitInterval) :
    geometricSurvival p 1 = ENNReal.ofReal (1 - (p : Real)) := by
  simp [geometricSurvival]

end ECRuntime
