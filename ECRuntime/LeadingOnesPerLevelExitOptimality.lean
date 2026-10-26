import ECRuntime.AdaptiveLeadingOnesLocalOptimalRate
import Mathlib

namespace ECRuntime

/-! P01: the calculus inequality needed to optimize the *certified* complete
adaptive LeadingOnes runtime formula. At level j>0, the exact exit mass is
p(1-p)^j; its maximum on [0,1] occurs at p=1/(j+1).

This is a genuine mathematical dependency, not a finite-state or statement
of the already certified full-runtime formula. -/

/-- The level-j exit probability is maximized by the reciprocal schedule. -/
theorem proposed_leadingOnes_levelExitMass_le_optimal
    (j : Nat) (hj : 0 < j) (p : Real)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) ^ j ≤
      (1 / ((j + 1 : Nat) : Real)) *
        (1 - 1 / ((j + 1 : Nat) : Real)) ^ j := by
  -- Stage 178 already certified the stronger endpoint-inclusive inequality
  -- using Mathlib's weighted real arithmetic-geometric mean theorem.
  have _hj : j ≠ 0 := Nat.ne_of_gt hj
  simpa only [one_div] using
    (proposed_leadingOnesAdaptive_localExitOptimality j p hp0 hp1)

end ECRuntime
