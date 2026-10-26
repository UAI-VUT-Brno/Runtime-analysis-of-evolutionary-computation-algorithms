import ECRuntime.LeadingOnesFixedTargetHalfIncrementBound
import ECRuntime.LeadingOnesFixedTargetCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 195 (PROPOSED, statement not yet approved): a quantitative lower
bound for every intermediate LeadingOnes target in the uniform-start
(1+1)-EA model. Induct over targets and sum the *certified* Stage 185
half-unit marginal cost. This is not a claim about every algorithm.
-/

/-- Every additional target level costs at least one half iteration in mean. -/
theorem proposed_leadingOnes_uniformFixedTarget_mean_atLeastHalfTarget
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k ≤ n) :
    (k : Real) / 2 ≤ leadingOnesUniformFixedTargetMean n p k := by
  suffices h : forall j : Nat, j ≤ n ->
      (j : Real) / 2 ≤ leadingOnesUniformFixedTargetMean n p j by
    exact h k hk
  intro j
  induction j with
  | zero =>
      intro _
      rw [proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum
        hp0 hp1 0 (Nat.zero_le n)]
      simp
  | succ j ih =>
      intro hsucc
      have hj : j < n := by omega
      have hprev := ih (Nat.le_of_lt hj)
      have hstep := proposed_leadingOnes_uniformFixedTarget_increment_atLeastHalf
        hp0 hp1 j hj
      have hcast : (((j + 1 : Nat) : Real)) / 2 = (j : Real) / 2 + 1 / 2 := by
        push_cast
        ring
      rw [hcast]
      linarith

end ECRuntime
