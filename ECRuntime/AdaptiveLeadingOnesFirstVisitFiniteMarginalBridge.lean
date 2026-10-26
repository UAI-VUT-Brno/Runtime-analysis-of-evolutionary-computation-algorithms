import ECRuntime.AdaptiveLeadingOnesFirstVisitMassEntry
import ECRuntime.AdaptiveLeadingOnesFiniteBelowEntryMarginal
import ECRuntime.AdaptiveLeadingOnesTrueFirstEntryConvolution
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01: the positive-time first-visit probability is represented by
an actual finite-cylinder path law. The certificate combines the
almost-everywhere no-return equivalence with the finite marginal theorem.
It does not assume uniform level visitation. -/

/-- A positive-time first visit has exactly the finite below-to-exact
path mass, even though the two infinite-path events need not coincide
pointwise outside the certified a.e. monotone support. -/
theorem proposed_leadingOnesAdaptive_firstVisitSucc_eq_finiteBelowExact
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i (t + 1)) =
    finiteTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
      (t + 1) x (leadingOnesFiniteBelowThenExactAtNextSet x i t) := by
  change transitionTrajectoryMeasure
    (leadingOnesAdaptiveTransition rate)
    (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
    {path : Nat → BitString n |
      leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
      ∀ s : Nat, s < t + 1 →
        leadingOnes (transitionTrajectoryState x path s) ≠ i.val} = _
  exact (proposed_leadingOnesAdaptive_firstVisitSuccMass_eq_belowEntryMass
    rate hrate x i t).trans
    (proposed_leadingOnesAdaptive_belowEntryMass_eq_finiteEntryMeasure
      rate hrate x i t)

end ECRuntime
