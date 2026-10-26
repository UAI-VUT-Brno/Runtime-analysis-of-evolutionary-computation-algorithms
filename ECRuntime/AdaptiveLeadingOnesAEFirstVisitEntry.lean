import ECRuntime.AdaptiveLeadingOnesAEScoreMonotone
import ECRuntime.MonotoneFirstVisitSucc
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. This transfers the deterministic first-entry equivalence to
the real adaptive Ionescu--Tulcea path measure. It is the null-set
component of the Stage 329 cylinder/finite-marginal bridge. -/

/-- Almost every adaptive trajectory first visits level `i` at time
`t+1` exactly when it advances to `i` from a lower score at time `t`. -/
theorem proposed_leadingOnesAdaptive_ae_firstVisitSucc_iff_below
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    ∀ᵐ path ∂transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x,
      (leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
        ∀ s : Nat, s < t + 1 →
          leadingOnes (transitionTrajectoryState x path s) ≠ i.val) ↔
      (leadingOnes (transitionTrajectoryState x path t) < i.val ∧
        leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val) := by
  filter_upwards [proposed_leadingOnesAdaptive_ae_scoreMonotone
    rate hrate x] with path hmono
  exact proposed_monotoneScore_firstVisitSucc_iff
    (fun k => leadingOnes (transitionTrajectoryState x path k))
    hmono i.val t

end ECRuntime
