import ECRuntime.LeadingOnesReferenceExitCostDecomposition
import ECRuntime.LeadingOnesBoundaryENNRealReciprocalBridge
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: a finite-sum continuity result.  Unlike the more ambitious Stage 420,
this theorem works exclusively with the explicit reference exit-cost formula;
there is no stochastic uniform-runtime expression to rewrite. -/

/-- The entire finite reference exit-cost sum converges termwise as the
level-zero rate approaches one from the admissible side. -/
theorem proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto
    (n : Nat) :
    Filter.Tendsto
      (fun base : Real => ∑ i : Fin n, (1 / 2 : ENNReal) *
        ENNReal.ofReal
          ((proposed_leadingOnes_referenceOptimalRate base i.val *
            (1 - proposed_leadingOnes_referenceOptimalRate base i.val) ^ i.val)⁻¹))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (∑ i : Fin n, if i.val = 0 then (1 / 2 : ENNReal) else
        (1 / 2 : ENNReal) * ENNReal.ofReal
          ((1 / ((i.val + 1 : Nat) : Real) *
            (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹))) := by
  classical
  have hterm (i : Fin n) : Filter.Tendsto
      (fun base : Real => if i.val = 0 then
        (1 / 2 : ENNReal) * ENNReal.ofReal (base⁻¹) else
        (1 / 2 : ENNReal) * ENNReal.ofReal
          ((1 / ((i.val + 1 : Nat) : Real) *
            (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (if i.val = 0 then (1 / 2 : ENNReal) else
        (1 / 2 : ENNReal) * ENNReal.ofReal
          ((1 / ((i.val + 1 : Nat) : Real) *
            (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹))) := by
    by_cases hi : i.val = 0
    · simpa only [hi, ite_true] using
        proposed_leadingOnes_referenceZero_ennrealBoundaryLimit
    · simpa only [hi, ite_false] using
        (tendsto_const_nhds : Filter.Tendsto
          (fun _base : Real => (1 / 2 : ENNReal) * ENNReal.ofReal
            ((1 / ((i.val + 1 : Nat) : Real) *
              (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹))
          (nhdsWithin (1 : Real) (Set.Iio 1))
          (nhds ((1 / 2 : ENNReal) * ENNReal.ofReal
            ((1 / ((i.val + 1 : Nat) : Real) *
              (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹))))
  have hsum := tendsto_finsetSum
    (Finset.univ : Finset (Fin n)) (fun i _ => hterm i)
  have hrewrite :
      (fun base : Real => ∑ i : Fin n, (1 / 2 : ENNReal) * ENNReal.ofReal
        ((proposed_leadingOnes_referenceOptimalRate base i.val *
          (1 - proposed_leadingOnes_referenceOptimalRate base i.val) ^ i.val)⁻¹)) =
      (fun base : Real => ∑ i : Fin n, if i.val = 0 then
        (1 / 2 : ENNReal) * ENNReal.ofReal (base⁻¹) else
        (1 / 2 : ENNReal) * ENNReal.ofReal
          ((1 / ((i.val + 1 : Nat) : Real) *
            (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹)) := by
    funext base
    exact proposed_leadingOnes_referenceExitCost_sum_decomposition n base
  rw [hrewrite]
  exact hsum

end ECRuntime
