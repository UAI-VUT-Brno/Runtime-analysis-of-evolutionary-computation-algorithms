import ECRuntime.OneMaxEANoFlipMaskWeight
import ECRuntime.Mutation
import Mathlib

namespace ECRuntime

/-! P07: quantitative self-loop probability for standard-bit mutation is
fitness-independent. It is a reusable ingredient for fixed-target waiting
time and geometric lower bounds. -/

/-- A (1+1)-EA with standard bit mutation retains its parent with probability
at least `(1-p)^n` whenever `0 ≤ p ≤ 1`, for any fitness function. -/
theorem proposed_onePlusOne_selfTransition_ge_emptyMask
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fitness : BitString n → Real) (x : BitString n) :
    (1 - p) ^ n ≤ (onePlusOneTransition p fitness) x x := by
  classical
  have hnonneg (mask : MutationMask n) :
      0 ≤ if selectedAfterMask fitness x mask = x then
          mutationMaskWeight p mask else 0 := by
    split_ifs
    · exact mutationMaskWeight_nonneg hp0 hp1 mask
    · exact le_refl 0
  have hterm :
      mutationMaskWeight p (∅ : MutationMask n) ≤
        ∑ mask : MutationMask n,
          if selectedAfterMask fitness x mask = x then
            mutationMaskWeight p mask else 0 := by
    have hs :
        (if selectedAfterMask fitness x (∅ : MutationMask n) = x then
            mutationMaskWeight p (∅ : MutationMask n) else 0) ≤
          ∑ mask : MutationMask n,
            if selectedAfterMask fitness x mask = x then
              mutationMaskWeight p mask else 0 := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun mask : MutationMask n =>
          if selectedAfterMask fitness x mask = x then
            mutationMaskWeight p mask else 0)
        (fun mask _ => hnonneg mask)
        (Finset.mem_univ (∅ : MutationMask n))
    simpa [proposed_oneMaxEA_emptyMask_selectedSelf] using hs
  calc
    (1 - p) ^ n = mutationMaskWeight p (∅ : MutationMask n) :=
      (proposed_oneMaxEA_emptyMask_exactWeight n p).symm
    _ ≤ ∑ mask : MutationMask n,
          if selectedAfterMask fitness x mask = x then
            mutationMaskWeight p mask else 0 := hterm
    _ = (onePlusOneTransition p fitness) x x := by
      rfl

end ECRuntime
