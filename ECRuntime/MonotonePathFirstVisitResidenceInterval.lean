import ECRuntime.FirstVisitFiniteMinimality
import Mathlib

namespace ECRuntime

/-!
P01: Deterministic occupation structure. For a monotone fitness path,
occupying a level at time `t` forces a unique contiguous residence block
starting at its first visit. This is a pathwise input to the later
probabilistic first-entrance disintegration, not an independence claim.
-/

/-- Every attained level of a nondecreasing integer trajectory has a first
visit, and the trajectory cannot leave that level and return before `t`. -/
theorem proposed_monotoneScore_firstVisitResidenceInterval
    (f : Nat → Nat) (hmono : Monotone f) (i t : Nat)
    (hit : f t = i) :
    ∃ k : Nat, k ≤ t ∧ f k = i ∧
      (∀ s : Nat, s < k → f s ≠ i) ∧
      (∀ s : Nat, k ≤ s → s ≤ t → f s = i) := by
  obtain ⟨k, hk, hki, hfirst⟩ :=
    proposed_discreteTrajectory_firstVisit_exists f i t hit
  refine ⟨k, hk, hki, hfirst, ?_⟩
  intro s hks hst
  have hlo : f k ≤ f s := hmono hks
  have hhi : f s ≤ f t := hmono hst
  omega

end ECRuntime
