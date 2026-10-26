import ECRuntime.AdaptiveLeadingOnesExpectedExactLevelResidence
import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: the actual uniform-start expected occupation of an exact
LeadingOnes level, after identifying genuine first visits and residence. -/

/-- Every nonterminal level has uniformly averaged expected occupation
equal to one-half its geometric conditional residence mean. -/
theorem proposed_leadingOnesAdaptive_uniformOccupation_eq_halfResidence
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        ∑' t : Nat,
          transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate
              (fun j hj => ⟨(hinterior j hj).1.le, (hinterior j hj).2.le⟩)) x
            {path : Nat → BitString n |
              leadingOnes (transitionTrajectoryState x path t) = i.val}) =
      (1 / 2 : ENNReal) *
        ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  rw [proposed_leadingOnesAdaptive_uniformExactLevelOccupation_eq_entryResidence
    n rate hinterior i]
  rw [proposed_leadingOnesAdaptive_eventualExactEntry_half rate hinterior i]

end ECRuntime
