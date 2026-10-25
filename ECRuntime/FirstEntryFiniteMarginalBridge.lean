import ECRuntime.AdaptiveLeadingOnesFiniteOccupationRenewal
import ECRuntime.FiniteMarginalIdentification
import ECRuntime.AdaptiveLeadingOnesFirstVisitMassEntry
import ECRuntime.AdaptiveLeadingOnesFiniteBelowEntryMarginal
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01. This is a strictly probabilistic prerequisite for Stage 321:
identifying the genuine infinite-path first-visit cylinder with the
finite-trajectory below-to-exact arrival mass. -/

/-- For nondecreasing adaptive LeadingOnes paths, an arrival from below
at time `t+1` is the first visit to that exact level, modulo null paths.
This measure identity requires a finite-cylinder marginal and the
almost-sure monotonicity argument; it is not a finite-sum identity. -/
theorem proposed_leadingOnesAdaptive_firstVisitCylinder_eq_finiteEntryMeasure
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
        ∀ s : Nat, s ≤ t →
          leadingOnes (transitionTrajectoryState x path s) ≠ i.val} =
    finiteTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
      (t + 1) x
      (leadingOnesFiniteBelowThenExactAtNextSet x i t) := by
  calc
    _ = transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) < i.val ∧
            leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val} := by
          simpa only [Nat.lt_succ_iff] using
            (proposed_leadingOnesAdaptive_firstVisitSuccMass_eq_belowEntryMass
              rate hrate x i t)
    _ = finiteTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
          (t + 1) x
          (leadingOnesFiniteBelowThenExactAtNextSet x i t) :=
        proposed_leadingOnesAdaptive_belowEntryMass_eq_finiteEntryMeasure
          rate hrate x i t

end ECRuntime
