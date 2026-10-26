import ECRuntime.AdaptiveLeadingOnesUniformEverVisitMass
import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: a genuine event-level theorem, not only a finite-history parity.
Combines the uniform ever-visit measure bridge and the certified exact
half-entry probability. -/

/-- A uniformly initialized adaptive LeadingOnes process ever visits any
fixed nonterminal level with probability exactly one half. -/
theorem proposed_leadingOnesAdaptive_uniformEverVisitMass_eq_half
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate
            (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)) x
          {path : Nat → BitString n |
            ∃ t : Nat, leadingOnes (transitionTrajectoryState x path t) = i.val}) =
      (1 / 2 : ENNReal) := by
  calc
    _ = leadingOnesAdaptiveEventualFirstCrossingExactMass rate i :=
      proposed_leadingOnesAdaptive_uniformEverVisitMass_eq_eventualExact
        n rate hrate i
    _ = (1 / 2 : ENNReal) :=
      proposed_leadingOnesAdaptive_eventualExactEntry_half rate hrate i

end ECRuntime
