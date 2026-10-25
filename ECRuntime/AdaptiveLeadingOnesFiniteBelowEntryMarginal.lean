import ECRuntime.GenericFiniteCylinderMarginal
import ECRuntime.LeadingOnesExactStayBranch
import ECRuntime.AdaptiveLeadingOnesFiniteOccupationRenewal
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. A genuinely finite-cylinder identification for the below-to-exact
entry event. Combined with the almost-sure first-visit equivalence from
Stages 341--343, this is intended to discharge the exact Stage 329
first-visit-versus-finite-entry measure identity. -/

/-- The probability of an adaptive LeadingOnes below-to-exact entry at
time `t+1` is exactly the explicitly weighted finite-path entry mass. -/
theorem proposed_leadingOnesAdaptive_belowEntryMass_eq_finiteEntryMeasure
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) < i.val ∧
        leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val} =
    finiteTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
      (t + 1) x (leadingOnesFiniteBelowThenExactAtNextSet x i t) := by
  classical
  have hevent : MeasurableSet
      (leadingOnesFiniteBelowThenExactAtNextSet x i t) :=
    (leadingOnesFiniteBelowThenExactAtNextSet x i t).to_countable.measurableSet
  have heq :
      ({path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) < i.val ∧
        leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val} :
        Set (Nat → BitString n)) =
      (transitionTrajectoryTail (t + 1)) ⁻¹'
        (leadingOnesFiniteBelowThenExactAtNextSet x i t) := by
    ext path
    change
      (leadingOnes (transitionTrajectoryState x path t) < i.val ∧
        leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val) ↔
      (leadingOnes
         (finiteTrajectoryEndpoint x t
           (Fin.init (transitionTrajectoryTail (t + 1) path))) < i.val ∧
       leadingOnes
         (finiteTrajectoryEndpoint x (t + 1)
           (transitionTrajectoryTail (t + 1) path)) = i.val)
    rw [Fin_init_transitionTrajectoryTail]
    simp only [finiteTrajectoryEndpoint_transitionTrajectoryTail]
  rw [heq]
  exact proposed_transitionTrajectoryMeasure_finiteCylinder_eq_finiteMeasure
    (leadingOnesAdaptiveTransition rate)
    (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
    x (t + 1) (leadingOnesFiniteBelowThenExactAtNextSet x i t) hevent

end ECRuntime
