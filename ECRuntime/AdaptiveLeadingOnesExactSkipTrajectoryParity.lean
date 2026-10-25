import ECRuntime.AdaptiveLeadingOnesUniformExactCrossingCylinderBridge
import ECRuntime.AdaptiveLeadingOnesFiniteCrossingParity
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: lift the exact-vs-skipped finite-history parity to an infinite
Markov trajectory cylinder, but only for exact-landing events. -/

/-- Uniformly averaged exact-first-crossing trajectory probability equals
the finite-history skip probability at the same time and boundary. -/
theorem proposed_leadingOnesAdaptive_uniformExactCylinder_eq_skipHistoryMass
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (t : Nat) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          (leadingOnesTrajectoryFirstCrossingExactSet i x t)) =
      ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingSkipMass (t := t) rate i) := by
  rw [proposed_leadingOnesAdaptive_uniformExactCrossingCylinder_eq_historyMass
    n rate hrate i t]
  rw [proposed_leadingOnesAdaptive_firstCrossingExactMass_eq_skipMass]

end ECRuntime
