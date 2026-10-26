import ECRuntime.UnrestrictedRuntime
import Mathlib

open scoped ENNReal

namespace ECRuntime

/-!
Stage 283 (P07, proposed). General target-set comparison for *genuine*
stochastic transition kernels, independent of OneMax, mutation strength or
elitist selection. It deliberately requires `IsStochastic P`: without
nonnegative transition weights, `expectedValueAfter_mono` is unavailable.

-/

/-- For a stochastic kernel, reaching a larger target cannot require more
expected truncated runtime. This is proved directly from the Bellman
recursion and `expectedValueAfter_mono`. -/
theorem proposed_finiteHorizonRuntime_antitone_target
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (s t : Set α)
    [DecidablePred (fun x => x ∈ s)]
    [DecidablePred (fun x => x ∈ t)]
    (hst : s ⊆ t) :
    ∀ (horizon : Nat) (x : α),
      finiteHorizonRuntime P t horizon x ≤
      finiteHorizonRuntime P s horizon x := by
  intro horizon
  induction horizon with
  | zero =>
      intro x
      simp
  | succ horizon ih =>
      intro x
      by_cases hxt : x ∈ t
      · rw [finiteHorizonRuntime_succ_of_mem P t horizon x hxt]
        exact finiteHorizonRuntime_nonneg P s hP (horizon + 1) x
      · have hxs : x ∉ s := fun hs => hxt (hst hs)
        rw [finiteHorizonRuntime_succ_of_not_mem P t horizon x hxt,
            finiteHorizonRuntime_succ_of_not_mem P s horizon x hxs]
        simpa only [add_comm] using
          (add_le_add_left
            (expectedValueAfter_mono P hP
              (finiteHorizonRuntime P t horizon)
              (finiteHorizonRuntime P s horizon) ih x) 1)

/-- The corresponding unrestricted comparison follows from Mathlib's
`iSup_le` and the exact `runtimeSup` definition, without finite-runtime
assumptions or cancellation of infinite values. -/
theorem proposed_runtimeSup_antitone_target
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (s t : Set α)
    [DecidablePred (fun x => x ∈ s)]
    [DecidablePred (fun x => x ∈ t)]
    (hst : s ⊆ t) (x : α) :
    runtimeSup P t x ≤ runtimeSup P s x := by
  unfold runtimeSup
  refine iSup_le ?_
  intro horizon
  exact (ENNReal.ofReal_le_ofReal
    (proposed_finiteHorizonRuntime_antitone_target P hP s t hst horizon x)).trans
      (le_iSup
        (fun k : Nat => ENNReal.ofReal (finiteHorizonRuntime P s k x)) horizon)

end ECRuntime
