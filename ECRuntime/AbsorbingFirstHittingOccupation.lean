import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 284 (P01, open). A generic pathwise first-hitting-time/occupation
identity for absorbing targets. This is deliberately independent of the
LeadingOnes objective and is the correct predecessor of Stage 282's
measure-theoretic `lintegral`/`tsum` interchange. The countable identity is supplied by a finite-support tsum calculation.
-/

/-- Nonmembership at the current time excludes every earlier target visit
when the target is absorbing. Pure temporal logic, no probability premise. -/
theorem proposed_absorbingPath_nonTarget_iff_allPrior_nonTarget
    {α : Type*} (target : Set α) (state : Nat → α)
    (habsorbing : ∀ t, state t ∈ target → state (t + 1) ∈ target)
    (t : Nat) :
    state t ∉ target ↔ ∀ k ≤ t, state k ∉ target := by
  induction t with
  | zero =>
      constructor
      · intro ht k hk
        have hk0 : k = 0 := by omega
        simpa [hk0] using ht
      · intro hall
        exact hall 0 le_rfl
  | succ t ih =>
      constructor
      · intro hnot
        have hprev : state t ∉ target := by
          intro ht
          exact hnot (habsorbing t ht)
        have hprior := ih.mp hprev
        intro k hk
        by_cases hlast : k = t + 1
        · simpa [hlast] using hnot
        · exact hprior k (by omega)
      · intro hall
        exact hall (t + 1) le_rfl

/-- For an absorbing target, the extended first hitting time equals the
countable sum of indicators of still being outside the target. This is
the pathwise identity needed for Mathlib's nonnegative `lintegral_tsum`.
This proof remains explicitly open, not an axiom. -/
theorem proposed_absorbingPath_firstHittingTime_eq_nonTargetTsum
    {α : Type*} (target : Set α)
    [DecidablePred (fun y => y ∈ target)]
    (x : α) (path : Nat → α)
    (habsorbing : ∀ t,
      transitionTrajectoryState x path t ∈ target →
      transitionTrajectoryState x path (t + 1) ∈ target) :
    transitionTrajectoryFirstHittingTime target x path =
      ∑' t : Nat,
        if transitionTrajectoryState x path t ∈ target
        then (0 : ENNReal) else 1 := by
  classical
  let state : Nat → α := transitionTrajectoryState x path
  have hstay : ∀ a b : Nat, a ≤ b → state a ∈ target → state b ∈ target := by
    intro a b hab ha
    induction b, hab using Nat.le_induction with
    | base => exact ha
    | succ b _ ih => exact habsorbing b ih
  by_cases hex : ∃ k : Nat, state k ∈ target
  · let k := Nat.find hex
    have hhit : state k ∈ target := Nat.find_spec hex
    have hiff (t : Nat) : state t ∈ target ↔ k ≤ t := by
      constructor
      · intro ht
        by_contra hnot
        exact (Nat.find_min hex (Nat.lt_of_not_ge hnot)) ht
      · intro hkt
        exact hstay k t hkt hhit
    have heqTerm : ∀ t : Nat,
        (if state t ∈ target then (0 : ENNReal) else 1) =
          (if t < k then (1 : ENNReal) else 0) := by
      intro t
      by_cases ht : t < k
      · simp [hiff, ht, not_le_of_gt ht]
      · have hkt : k ≤ t := Nat.le_of_not_gt ht
        simp [hiff, ht, hkt]
    have hseries :
        (∑' t : Nat, if state t ∈ target then (0 : ENNReal) else 1) =
          (k : ENNReal) := by
      simp_rw [heqTerm]
      rw [tsum_eq_sum (s := Finset.range k) (by
        intro t ht
        have hkt : k ≤ t := Nat.le_of_not_gt (by
          intro hlt
          exact ht (Finset.mem_range.mpr hlt))
        simp [Nat.not_lt.mpr hkt])]
      have hfilter :
          (Finset.range k).filter (fun t => t < k) = Finset.range k := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, and_self]
      simp [hfilter]
    unfold transitionTrajectoryFirstHittingTime
    rw [dif_pos hex]
    change ENNReal.ofReal (Nat.find hex : Real) = _
    simpa [k, state] using hseries.symm
  · have hnever : ∀ t : Nat, state t ∉ target := by
      intro t ht
      exact hex ⟨t, ht⟩
    have hseries :
        (∑' t : Nat, if state t ∈ target then (0 : ENNReal) else 1) = ⊤ := by
      simp [hnever]
    unfold transitionTrajectoryFirstHittingTime
    rw [dif_neg hex]
    simpa [state] using hseries.symm

end ECRuntime
