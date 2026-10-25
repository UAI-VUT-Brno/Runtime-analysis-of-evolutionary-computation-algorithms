import ECRuntime.AdaptiveLeadingOnesAEScoreMonotone
import ECRuntime.AdaptiveLeadingOnesTrueFirstEntryConvolution
import ECRuntime.LeadingOnesExactEntryStep
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. The first-visit event is different from the first-crossing-exact
cylinder off the support of monotone trajectories. The Markov law is
concentrated on that support, and hence their masses agree. This turns
the actual first-visit event into the finite-history cylinder required
for the uniform first-entry identification in Stage 367. -/

/-- A genuine first visit to level `i` at *any* time agrees in measure
with the historical first crossing of boundary `i` that lands at `i`.
No pointwise equality of the event sets is asserted. -/
theorem proposed_leadingOnesAdaptive_firstVisitMass_eq_exactCrossingCylinder
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i t) =
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
      (leadingOnesTrajectoryFirstCrossingExactSet i x t) := by
  apply measure_congr
  filter_upwards [proposed_leadingOnesAdaptive_ae_scoreMonotone
    rate hrate x] with path hmono
  apply propext
  refine Iff.trans ?_
    (mem_leadingOnesTrajectoryFirstCrossingExactSet_iff i x t path).symm
  change
    (leadingOnes (transitionTrajectoryState x path t) = i.val ∧
      ∀ s : Nat, s < t →
        leadingOnes (transitionTrajectoryState x path s) ≠ i.val) ↔
    ((∀ s : Nat, s < t →
        leadingOnes (transitionTrajectoryState x path s) < i.val) ∧
      leadingOnes (transitionTrajectoryState x path t) = i.val)
  constructor
  · rintro ⟨ht, hbefore⟩
    refine ⟨?_, ht⟩
    intro s hs
    have hle : leadingOnes (transitionTrajectoryState x path s) ≤ i.val := by
      calc
        leadingOnes (transitionTrajectoryState x path s) ≤
            leadingOnes (transitionTrajectoryState x path t) :=
          hmono (Nat.le_of_lt hs)
        _ = i.val := ht
    have hne := hbefore s hs
    omega
  · rintro ⟨hbefore, ht⟩
    refine ⟨ht, ?_⟩
    intro s hs
    exact ne_of_lt (hbefore s hs)

end ECRuntime
