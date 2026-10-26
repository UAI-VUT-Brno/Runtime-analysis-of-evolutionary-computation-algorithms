import ECRuntime.FirstVisitFiniteMinimality
import Mathlib

namespace ECRuntime

/-! P01. Exact uniqueness of the first-visit index, independently of the
transition kernel. The probabilistic calculation can therefore partition
by a unique index without double-counting first visits. -/

/-- If a score occurs by time `t`, exactly one index is its first visit. -/
theorem proposed_discreteTrajectory_firstVisit_existsUnique
    (f : Nat → Nat) (i t : Nat) (hit : f t = i) :
    ∃! k : Nat, k ≤ t ∧ f k = i ∧
      ∀ s : Nat, s < k → f s ≠ i := by
  obtain ⟨k, hk, hki, hfirst⟩ :=
    proposed_discreteTrajectory_firstVisit_exists f i t hit
  refine ⟨k, ⟨hk, hki, hfirst⟩, ?_⟩
  intro m hm
  rcases hm with ⟨_hmle, hmi, hmfirst⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfirst m hlt hmi
  · exact hmfirst k hgt hki

end ECRuntime
