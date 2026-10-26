import ECRuntime.AdaptiveLeadingOnesFirstVisitMassCountablePartition
import ECRuntime.AdaptiveLeadingOnesUniformTrueFirstEntryMass
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: identify the genuine uniform-start probability of ever visiting
an exact nonterminal level, rather than just a sum of first-entry masses. -/

/-- Uniform-start probability of ever visiting level `i` is the exact
first-crossing mass, for any strictly interior adaptive schedule. -/
theorem proposed_leadingOnesAdaptive_uniformEverVisitMass_eq_eventualExact
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
      leadingOnesAdaptiveEventualFirstCrossingExactMass rate i := by
  classical
  calc
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate
              (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)) x
            {path : Nat → BitString n |
              ∃ t : Nat, leadingOnes (transitionTrajectoryState x path t) = i.val}) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, ∑' t : Nat,
          transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate
              (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)) x
            (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i t)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        exact proposed_leadingOnesAdaptive_everVisitMeasure_eq_firstVisitTsum
          n rate (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩) x i
    _ = leadingOnesAdaptiveEventualFirstCrossingExactMass rate i :=
      proposed_leadingOnesAdaptive_uniformTrueFirstVisitMass_eq_eventualExactEntry
        n rate hrate i

end ECRuntime
