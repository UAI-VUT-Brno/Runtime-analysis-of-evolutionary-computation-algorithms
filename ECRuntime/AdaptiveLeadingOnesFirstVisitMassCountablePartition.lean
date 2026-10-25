import ECRuntime.AdaptiveLeadingOnesTrueFirstEntryConvolution
import ECRuntime.FirstVisitSetsDisjoint
import ECRuntime.GenericMarkovFirstEntryOneStepMass
import ECRuntime.EventualExactLevelEntry
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-!
P01: genuine measure-theoretic partition of a level's ever-visited
event by the unique first visit time. Stage 367 needs this identity to
identify the resulting countable mass with the paper's exact-entry
averages. This is a proposed new research target, not certified code.
-/

/-- The probability of ever occupying a given exact nonterminal score
is the sum of its genuine first-entrance probabilities over all times. -/
theorem proposed_leadingOnesAdaptive_everVisitMeasure_eq_firstVisitTsum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) :
    transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          ∃ t : Nat, leadingOnes (transitionTrajectoryState x path t) = i.val} =
      ∑' t : Nat,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i t) := by
  classical
  let V : BitString n → Nat := fun y => leadingOnes y + 1
  have heq (t : Nat) :
      transitionTrajectoryFirstExactLevelEntrySet V x i t =
        proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i t := by
    ext path
    change (leadingOnes (transitionTrajectoryState x path t) + 1 = i.val + 1 ∧
        ∀ s : Nat, s < t →
          leadingOnes (transitionTrajectoryState x path s) + 1 ≠ i.val + 1) ↔
      (leadingOnes (transitionTrajectoryState x path t) = i.val ∧
        ∀ s : Nat, s < t →
          leadingOnes (transitionTrajectoryState x path s) ≠ i.val)
    simp
  have hevent :
      {path : Nat → BitString n |
          ∃ t : Nat, leadingOnes (transitionTrajectoryState x path t) = i.val} =
        transitionTrajectoryEventuallyVisitsExactLevelSet V x i := by
    ext path
    simp only [Set.mem_setOf_eq, transitionTrajectoryEventuallyVisitsExactLevelSet,
      Set.mem_iUnion, transitionTrajectoryFirstExactLevelEntrySet,
      Set.mem_setOf_eq, transitionTrajectoryFirstVisitsExactLevelAt]
    constructor
    · rintro ⟨t, ht⟩
      have h : ∃ t : Nat,
          V (transitionTrajectoryState x path t) = i.val + 1 := by
        exact ⟨t, by simpa [V] using congrArg Nat.succ ht⟩
      refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
      intro s hs
      exact Nat.find_min h hs
    · rintro ⟨t, ht, _hbefore⟩
      refine ⟨t, ?_⟩
      exact Nat.add_right_cancel (show
        leadingOnes (transitionTrajectoryState x path t) + 1 = i.val + 1
        from ht)
  rw [hevent]
  unfold transitionTrajectoryEventuallyVisitsExactLevelSet
  rw [measure_iUnion
    (pairwise_disjoint_transitionTrajectoryFirstExactLevelEntrySet V x i)
    (fun t => measurableSet_transitionTrajectoryFirstExactLevelEntrySet V x i t)]
  apply tsum_congr
  intro t
  rw [heq t]

end ECRuntime
