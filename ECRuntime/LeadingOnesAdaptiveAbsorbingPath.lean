import ECRuntime.LeadingOnes
import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.AdaptiveLeadingOnesLocalRenewalKernel
import Mathlib

namespace ECRuntime

/-!
Stage 287 (P01, proposed). Separate the deterministic target-membership
algebra from the measure-theoretic pathwise occupation theorem. The
nonoptimal/target equivalence is also established in the open Stage 282,
but this standalone lemma can be certified independently and reused by
other evolutionary processes whose optimum is the all-ones string.
-/

/-- A LeadingOnes state is below the optimal score exactly when it does
not belong to the optimum target. -/
theorem proposed_leadingOnes_lt_dim_iff_not_target
    {n : Nat} (x : BitString n) :
    leadingOnes x < n ↔ x ∉ leadingOnesTarget n := by
  constructor
  · intro hlt hx
    change x = allOnes n at hx
    subst x
    simp [leadingOnes_allOnes] at hlt
  · intro hx
    have hle : leadingOnes x ≤ n := leadingOnes_le x
    have hne : leadingOnes x ≠ n := by
      intro heq
      exact hx ((leadingOnes_eq_dim_iff x).mp heq)
    omega

end ECRuntime
