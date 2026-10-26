import ECRuntime.AdaptiveLeadingOnesUniformEverVisitHalf
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: an event-level law, uniform over *every pair* of strictly
interior adaptive mutation schedules, not merely a recurrence of finite masses. -/

/-- Uniform-start eventual visitation of an exact nonterminal level is
invariant under arbitrary changes of an interior level-dependent rate. -/
theorem proposed_leadingOnesAdaptive_uniformEverVisit_invariant_between_rates
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate₁ rate₂ : Nat → Real)
    (h₁ : ∀ j : Nat, j ≤ n → 0 < rate₁ j ∧ rate₁ j < 1)
    (h₂ : ∀ j : Nat, j ≤ n → 0 < rate₂ j ∧ rate₂ j < 1)
    (i : Fin n) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate₁)
          (proposed_leadingOnesAdaptive_transition_stochastic rate₁
            (fun j hj => ⟨(h₁ j hj).1.le, (h₁ j hj).2.le⟩)) x
          {path : Nat → BitString n |
            ∃ t : Nat, leadingOnes (transitionTrajectoryState x path t) = i.val}) =
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate₂)
          (proposed_leadingOnesAdaptive_transition_stochastic rate₂
            (fun j hj => ⟨(h₂ j hj).1.le, (h₂ j hj).2.le⟩)) x
          {path : Nat → BitString n |
            ∃ t : Nat, leadingOnes (transitionTrajectoryState x path t) = i.val}) := by
  rw [proposed_leadingOnesAdaptive_uniformEverVisitMass_eq_half n rate₁ h₁ i]
  rw [proposed_leadingOnesAdaptive_uniformEverVisitMass_eq_half n rate₂ h₂ i]

end ECRuntime
