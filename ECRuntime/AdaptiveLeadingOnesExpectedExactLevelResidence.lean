import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import ECRuntime.AdaptiveLeadingOnesConditionalResidenceMean
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.AdaptiveLeadingOnesFirstEntryResidenceTsum
import ECRuntime.AdaptiveLeadingOnesUniformTrueFirstEntryMass
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! Stage 305 (P01 research). This is the actual missing expected-level
occupation factorization, not an algebraic proxy. Its proof must combine
first-entry probability, a no-return property, and geometric residence
of the level under the adaptive transition kernel. -/

/-- For an interior fitness-dependent mutation schedule, uniformly averaged
countable occupation at one level equals its first-visit probability times
its geometric residence mean. -/
theorem proposed_leadingOnesAdaptive_uniformExactLevelOccupation_eq_entryResidence
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
      leadingOnesAdaptiveEventualFirstCrossingExactMass rate i *
        ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  let residence : ENNReal :=
    ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹)
  let hrate0 : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1 :=
    fun j hj => ⟨(hinterior j hj).1.le, (hinterior j hj).2.le⟩
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate0
  let occupation (x : BitString n) : ENNReal :=
    ∑' t : Nat, transitionTrajectoryMeasure P hP x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) = i.val}
  let entry (x : BitString n) : ENNReal :=
    ∑' k : Nat, transitionTrajectoryMeasure P hP x
      (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i k)
  have hfixed (x : BitString n) : occupation x = entry x * residence := by
    exact proposed_leadingOnesAdaptive_fixedStartLevelOccupation_eq_firstVisitMass_mul_residence
      n rate hinterior x i
  have huniform :
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ x : BitString n, entry x) =
        leadingOnesAdaptiveEventualFirstCrossingExactMass rate i := by
    simpa only [entry, P, hP, hrate0,
      proposed_leadingOnesAdaptive_firstVisitAtTimeSet] using
      proposed_leadingOnesAdaptive_uniformTrueFirstVisitMass_eq_eventualExactEntry
        n rate hinterior i
  change ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n, occupation x) =
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate i * residence
  calc
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, occupation x) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, entry x * residence) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          exact hfixed x
    _ = (((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, entry x)) * residence := by
          rw [← Finset.sum_mul]
          ac_rfl
    _ = leadingOnesAdaptiveEventualFirstCrossingExactMass rate i * residence := by
          rw [huniform]

end ECRuntime
