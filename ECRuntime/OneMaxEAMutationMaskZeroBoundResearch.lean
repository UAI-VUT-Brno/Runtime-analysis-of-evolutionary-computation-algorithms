import ECRuntime.Mutation
import ECRuntime.OneMax
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-!
P07: a deterministic bound on accepted multi-bit progress. It counts
coordinates which were zero *before* mutation and flipped by the mask;
this is not the total mask radius and it does not assume independence.
-/

/-- The old zero set is covered by the new zero set together with the
flipped old-zero coordinates. This remains valid for rejected masks. -/
private theorem proposed_oneMax_oldZero_set_subset_newZero_union_flipped
    {n : Nat} (x : BitString n) (mask : MutationMask n) :
    zeroPositions x ⊆
      zeroPositions (mutateWithMask x mask) ∪ (zeroPositions x ∩ mask) := by
  intro i hi
  by_cases hm : i ∈ mask
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hi, hm⟩))
  · have hx : x i = false := (mem_zeroPositions x i).mp hi
    have hy : mutateWithMask x mask i = false := by
      simp [mutateWithMask, hm, hx]
    exact Finset.mem_union.mpr
      (Or.inl ((mem_zeroPositions (mutateWithMask x mask) i).mpr hy))

/-- Consequently, the raw mutation can eliminate at most the old zeros
which it flips, irrespective of simultaneous one-to-zero mutations. -/
private theorem proposed_oneMax_rawZeroDecrease_le_flippedZeroCount
    {n : Nat} (x : BitString n) (mask : MutationMask n) :
    (zeroCount x : Real) - (zeroCount (mutateWithMask x mask) : Real) ≤
      ((zeroPositions x ∩ mask).card : Real) := by
  have hsub := proposed_oneMax_oldZero_set_subset_newZero_union_flipped x mask
  have hcard : zeroCount x ≤
      zeroCount (mutateWithMask x mask) + (zeroPositions x ∩ mask).card := by
    calc
      zeroCount x = (zeroPositions x).card := (zeroPositions_card x).symm
      _ ≤ (zeroPositions (mutateWithMask x mask) ∪
          (zeroPositions x ∩ mask)).card := Finset.card_le_card hsub
      _ ≤ (zeroPositions (mutateWithMask x mask)).card +
          (zeroPositions x ∩ mask).card := Finset.card_union_le _ _
      _ = zeroCount (mutateWithMask x mask) +
          (zeroPositions x ∩ mask).card := by rw [zeroPositions_card]
  have hr : (zeroCount x : Real) ≤
      (zeroCount (mutateWithMask x mask) : Real) +
        ((zeroPositions x ∩ mask).card : Real) := by
    exact_mod_cast hcard
  linarith

/-- OneMax elitist selection cannot remove more zeros than the original
currently-zero coordinates toggled by the mutation mask. -/
theorem proposed_oneMax_selectedZeroDecrease_le_flippedZeroCount
    {n : Nat} (x : BitString n) (mask : MutationMask n) :
    (zeroCount x : Real) -
        (zeroCount (selectedAfterMask oneMaxReal x mask) : Real) ≤
      ((zeroPositions x ∩ mask).card : Real) := by
  by_cases hacc : oneMaxReal x ≤ oneMaxReal (mutateWithMask x mask)
  · simpa [selectedAfterMask, elitistSelect, hacc] using
      (proposed_oneMax_rawZeroDecrease_le_flippedZeroCount x mask)
  · simp [selectedAfterMask, elitistSelect, hacc]

end ECRuntime
