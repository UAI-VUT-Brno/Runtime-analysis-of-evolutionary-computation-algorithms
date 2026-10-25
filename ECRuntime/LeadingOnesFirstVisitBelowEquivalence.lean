import ECRuntime.MonotoneFirstVisitSucc
import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.LeadingOnes
import Mathlib

namespace ECRuntime

/-! P01. A pathwise ingredient of Stage 329: first entry at positive time is
precisely entry from below on monotone paths. Almost-sure monotonicity and the
cylinder measure identification remain separate obligations. -/

/-- Along a score-monotone LeadingOnes trajectory, first visiting exact
level `i` at `t+1` is equivalent to entering from a strictly lower level. -/
theorem proposed_leadingOnes_firstVisitSucc_iff_below_of_monotone
    {n : Nat} (x : BitString n) (path : Nat → BitString n)
    (hmono : Monotone (fun k =>
      leadingOnes (transitionTrajectoryState x path k)))
    (i : Fin n) (t : Nat) :
    (leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
      ∀ s : Nat, s < t + 1 →
        leadingOnes (transitionTrajectoryState x path s) ≠ i.val) ↔
    (leadingOnes (transitionTrajectoryState x path t) < i.val ∧
      leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val) := by
  exact proposed_monotoneScore_firstVisitSucc_iff
    (fun k => leadingOnes (transitionTrajectoryState x path k)) hmono i.val t

end ECRuntime
