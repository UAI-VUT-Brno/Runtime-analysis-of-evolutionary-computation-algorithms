import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import ECRuntime.Mutation
import Mathlib

namespace ECRuntime

/-! P07. Exact empty-mask atom for independent standard-bit mutation.
This is the concrete kernel ingredient of Stage 307's nontrivial one-step
survival bound, not a generic consequence of target inclusion. -/

/-- Independent bit mutation leaves every bit unchanged with probability
`(1-p)^n`, including the zero-dimensional and endpoint-rate cases. -/
theorem proposed_oneMaxEA_emptyMask_exactWeight
    (n : Nat) (p : Real) :
    mutationMaskWeight p (∅ : MutationMask n) = (1-p)^n := by
  simp [mutationMaskWeight]

/-- The empty mutation mask leaves the elitist (1+1)-EA at its current point
for any fitness function; its probability is given by the preceding theorem. -/
theorem proposed_oneMaxEA_emptyMask_selectedSelf
    {n : Nat} (fitness : BitString n → Real) (x : BitString n) :
    selectedAfterMask fitness x (∅ : MutationMask n) = x := by
  simp [selectedAfterMask, elitistSelect]

end ECRuntime
