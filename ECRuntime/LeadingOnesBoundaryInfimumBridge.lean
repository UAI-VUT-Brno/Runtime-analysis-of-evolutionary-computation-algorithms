import ECRuntime.LeadingOnesReferenceExitCostDecomposition
import ECRuntime.LeadingOnesBoundaryENNRealReciprocalBridge
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: this candidate isolates the future Stage-420 boundary argument.
The remaining step is finite-dimensional `tendsto_finsetSum`, made
available in a separate approved Stage-456 source. No continuity of
ENNReal multiplication at 0 * infinity is assumed. -/

/-- Conditional boundary infimum statement, with the precise finite-cost
limit as a hypothesis. This theorem records the runtime-to-cost reduction;
its hypothesis is deliberately explicit and cannot certify Stage 420. -/
theorem proposed_leadingOnes_boundaryRuntime_limit_of_costLimit
    (n : Nat) (hn : 0 < n)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hinterior : ∀ᶠ base in (nhdsWithin (1 : Real) (Set.Iio 1)),
      ∀ j : Nat, j ≤ n →
        0 < proposed_leadingOnes_referenceOptimalRate base j ∧
          proposed_leadingOnes_referenceOptimalRate base j < 1)
    (hcost : Filter.Tendsto
      (fun base : Real => ∑ i : Fin n,
        (1 / 2 : ENNReal) *
          ENNReal.ofReal
            ((proposed_leadingOnes_referenceOptimalRate base i.val *
              (1 - proposed_leadingOnes_referenceOptimalRate base i.val) ^ i.val)⁻¹))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (∑ i : Fin n, if i.val = 0 then (1 / 2 : ENNReal) else
        (1 / 2 : ENNReal) * ENNReal.ofReal
          ((1 / ((i.val + 1 : Nat) : Real) *
            (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹)))) :
    Filter.Tendsto
      (fun base : Real =>
        ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          ∑ x : BitString n,
            runtimeSup (leadingOnesAdaptiveTransition
              (proposed_leadingOnes_referenceOptimalRate base))
              (leadingOnesTarget n) x)
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (∑ i : Fin n, if i.val = 0 then (1 / 2 : ENNReal) else
        (1 / 2 : ENNReal) * ENNReal.ofReal
          ((1 / ((i.val + 1 : Nat) : Real) *
            (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹))) := by
  have _hpositiveDimension : 0 < n := hn
  apply hcost.congr'
  filter_upwards [hinterior] with base hb
  exact (proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum
    n (proposed_leadingOnes_referenceOptimalRate base) hb).symm

end ECRuntime
