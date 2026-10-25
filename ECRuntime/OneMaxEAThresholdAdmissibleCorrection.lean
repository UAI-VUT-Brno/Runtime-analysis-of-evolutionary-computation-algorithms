import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import Mathlib

namespace ECRuntime

/-!
Corrected replacement proposal for historically frozen, false Stage 281.
The Stage 281 unrestricted-rate theorem was disproved by an exact rational
counterexample. This approved compatibility replacement uses the hypotheses
required for a stochastic mutation kernel, already certified in Stage 286.
The original false claim is retained verbatim in candidates/retired/ for audit.
-/

/-- Stage 281's valid zero-count target set. -/
def oneMaxZeroThreshold {n : Nat} (r : Nat) : Set (BitString n) :=
  {x | oneMaxPotential x ≤ r}

/-- Valid historical Stage 281 inclusion lemma, migrated unchanged. -/
theorem proposed_oneMaxZeroThreshold_mono
    {n : Nat} (r s : Nat) (hrs : r ≤ s) :
    oneMaxZeroThreshold (n := n) r ⊆ oneMaxZeroThreshold (n := n) s := by
  intro x hx
  exact le_trans hx hrs

/-- The valid target monotonicity theorem for standard bit mutation.
    Its essential extra hypotheses are `0 ≤ p` and `p ≤ 1`. -/
theorem proposed_oneMaxEA_runtimeSup_antitone_threshold_corrected
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Nat) (hrs : r ≤ s) (x : BitString n) :
    runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
      {y : BitString n | oneMaxPotential y ≤ s} x ≤
    runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
      {y : BitString n | oneMaxPotential y ≤ r} x := by
  exact proposed_oneMaxEA_runtimeSup_antitone_threshold_admissible
    p hp0 hp1 r s hrs x

end ECRuntime
