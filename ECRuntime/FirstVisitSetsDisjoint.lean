import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.LeadingOnes
import Mathlib

namespace ECRuntime

/-- First-visit events at distinct trajectory times cannot occur together,
regardless of the adaptive transition law. -/
theorem proposed_discreteTrajectory_firstVisitTime_unique
    {n : Nat} (x : BitString n) (i : Fin n)
    (k m : Nat) (hkm : k < m)
    (path : Nat → BitString n)
    (hk : leadingOnes (transitionTrajectoryState x path k) = i.val)
    (hm : leadingOnes (transitionTrajectoryState x path m) = i.val ∧
      ∀ s : Nat, s < m →
        leadingOnes (transitionTrajectoryState x path s) ≠ i.val) : False := by
  exact (hm.2 k hkm) hk

end ECRuntime
