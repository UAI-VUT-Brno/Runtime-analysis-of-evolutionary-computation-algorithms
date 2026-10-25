import ECRuntime.GenericTargetRuntimeAntitonicity
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-!
Stage 286 (P07, proposed, dependent on Stage 283). The corrected form
of Stage 281's non-RLS fixed-target claim. Stochastic bit mutation
requires `0 ≤ p ≤ 1`; these hypotheses cannot simply be added to
Stage 281 because its approved theorem statement is frozen.
-/

/-- OneMax target with at most `r` remaining zero coordinates. -/
def oneMaxEAZeroAtMost {n : Nat} (r : Nat) : Set (BitString n) :=
  {x | oneMaxPotential x ≤ r}

instance instDecidablePredOneMaxEAZeroAtMost {n : Nat} (r : Nat) :
    DecidablePred (fun x : BitString n => x ∈ oneMaxEAZeroAtMost (n := n) r) := by
  intro x
  change Decidable (oneMaxPotential x ≤ r)
  infer_instance

/-- Increasing the allowable residual zero count weakly decreases
unrestricted hitting time for a genuine stochastic multi-bit-mutation EA. -/
theorem proposed_oneMaxEA_runtimeSup_antitone_threshold_admissible
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Nat) (hrs : r ≤ s) (x : BitString n) :
    runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
      (oneMaxEAZeroAtMost (n := n) s) x ≤
    runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
      (oneMaxEAZeroAtMost (n := n) r) x := by
  apply proposed_runtimeSup_antitone_target
    (onePlusOneTransition p (oneMaxReal (n := n)))
    (onePlusOneTransition_stochastic hp0 hp1 (oneMaxReal (n := n)))
    (oneMaxEAZeroAtMost (n := n) r)
    (oneMaxEAZeroAtMost (n := n) s)
  · intro y hy
    exact le_trans hy hrs

end ECRuntime
