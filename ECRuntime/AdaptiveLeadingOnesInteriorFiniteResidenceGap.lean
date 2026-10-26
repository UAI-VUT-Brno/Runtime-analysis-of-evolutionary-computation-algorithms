import ECRuntime.AdaptiveLeadingOnesBoundaryPerturbationCost
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 252 (P01): proposed, NOT yet approved.
The epsilon perturbation changes only score zero. Thus the *whole finite
residence surrogate* differs from the boundary-optimal surrogate by precisely
epsilon/(1-epsilon). This is an algebraic statement, not yet a runtime theorem:
the trajectory occupation identity in Stage 245 remains open.
-/

/-- Exact perturbation gap in the finite sum of reciprocal exit rates. -/
theorem proposed_leadingOnesAdaptive_interiorFiniteResidenceGap
    (n : Nat) (hn : 0 < n) (eps : Real)
    (heps0 : 0 < eps) (heps1 : eps < 1) :
    (∑ i : Fin n,
      ((leadingOnesInteriorApproxSchedule eps i.val *
          (1 - leadingOnesInteriorApproxSchedule eps i.val) ^ i.val)⁻¹ -
        (leadingOnesLocallyOptimalSchedule i.val *
          (1 - leadingOnesLocallyOptimalSchedule i.val) ^ i.val)⁻¹)) =
      eps / (1 - eps) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  calc
    (∑ i : Fin n,
      ((leadingOnesInteriorApproxSchedule eps i.val *
          (1 - leadingOnesInteriorApproxSchedule eps i.val) ^ i.val)⁻¹ -
        (leadingOnesLocallyOptimalSchedule i.val *
          (1 - leadingOnesLocallyOptimalSchedule i.val) ^ i.val)⁻¹)) =
      ((leadingOnesInteriorApproxSchedule eps i0.val *
          (1 - leadingOnesInteriorApproxSchedule eps i0.val) ^ i0.val)⁻¹ -
        (leadingOnesLocallyOptimalSchedule i0.val *
          (1 - leadingOnesLocallyOptimalSchedule i0.val) ^ i0.val)⁻¹) := by
        apply Finset.sum_eq_single i0
        · intro i _hi hneq
          have hnonzero : i.val ≠ 0 := by
            intro hz
            apply hneq
            exact Fin.ext hz
          simp [leadingOnesInteriorApproxSchedule, hnonzero]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ i0))
    _ = eps / (1 - eps) := by
      simpa only [i0] using
        (proposed_leadingOnesAdaptive_interiorZeroResidenceGap eps heps0 heps1)

end ECRuntime
