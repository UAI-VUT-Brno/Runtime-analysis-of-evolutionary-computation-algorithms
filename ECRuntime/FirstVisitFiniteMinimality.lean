import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

namespace ECRuntime

/-! P01. Minimal first entry is a deterministic path property; no
probabilistic independence hypothesis is hidden in this reduction. -/

/-- A trajectory seen at a given level at time `t` has a least first
visit at or before `t`. The argument is independent of the Markov law. -/
theorem proposed_discreteTrajectory_firstVisit_exists
    (f : Nat → Nat) (i t : Nat) (hit : f t = i) :
    ∃ k : Nat, k ≤ t ∧ f k = i ∧
      ∀ s : Nat, s < k → f s ≠ i := by
  classical
  have hmain : ∀ u : Nat, (∃ s : Nat, s ≤ u ∧ f s = i) →
      ∃ k : Nat, k ≤ u ∧ f k = i ∧ ∀ s : Nat, s < k → f s ≠ i := by
    intro u
    induction u with
    | zero =>
        rintro ⟨s, hs, hsi⟩
        have hs0 : s = 0 := by omega
        subst s
        refine ⟨0, le_rfl, hsi, ?_⟩
        intro v hv
        omega
    | succ u ih =>
        intro h
        by_cases hprev : ∃ s : Nat, s ≤ u ∧ f s = i
        · obtain ⟨k, hk, hki, hbefore⟩ := ih hprev
          exact ⟨k, by omega, hki, hbefore⟩
        · have hu : f (u + 1) = i := by
            obtain ⟨s, hs, hsi⟩ := h
            have heq : s = u + 1 := by
              by_contra hne
              apply hprev
              exact ⟨s, by omega, hsi⟩
            simpa [heq] using hsi
          refine ⟨u + 1, le_rfl, hu, ?_⟩
          intro s hs hsi
          exact hprev ⟨s, by omega, hsi⟩
  exact hmain t ⟨t, le_rfl, hit⟩

end ECRuntime
