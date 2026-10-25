import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.LeadingOnesExit
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-!
P07: unresolved independent-bit specialization of the already certified
static-unary-unbiased coordinate marginal. The certified identity is
`coordinateFlipMass = meanRadius / n`; this stage seeks the exact
independent-bit identity without assuming `n > 0`, and should be used
before the mask-expectation step in Stage 357. This is NOT a public lemma.
-/

/-- A specified coordinate in independent bit mutation is flipped with
probability exactly `p`. The all-zero-dimensional case is vacuous as
there is no `i : Fin 0`. -/
theorem proposed_independentBitLaw_coordinateFlipMass_eq_p
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    (StaticUnaryUnbiasedMutation.independentBitLaw (n := n) p hp0 hp1).coordinateFlipMass i
      = p := by
  classical
  -- Every Fin n is nonempty here: reduce by unary-unbiased symmetry to
  -- coordinate 0, then use the already certified exact exit-mask sum.
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let j0 : Fin n := ⟨0, hn⟩
  let law : StaticUnaryUnbiasedMutation n :=
    StaticUnaryUnbiasedMutation.independentBitLaw p hp0 hp1
  have hevent (mask : MutationMask n) :
      leadingOnesExitMaskEvent j0 mask ↔ j0 ∈ mask := by
    constructor
    · exact And.left
    · intro hj
      refine ⟨hj, ?_⟩
      intro j hlt
      have hzero : j0.val = 0 := rfl
      omega
  have hfamily :
      ((Finset.univ : Finset (MutationMask (n - (j0.val + 1)))).image
        (leadingOnesExitMask j0)) =
      (Finset.univ : Finset (MutationMask n)).filter
        (fun mask => j0 ∈ mask) := by
    ext mask
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨suffix, hmask⟩
      rw [← hmask]
      exact leadingOnesExitMask_level_mem j0 suffix
    · intro hmask
      refine ⟨leadingOnesExitSuffixOfMask j0 mask, ?_⟩
      exact leadingOnesExitMask_suffixOfMask_eq_of_event j0 mask
        ((hevent mask).2 hmask)
  have hmass0 : law.coordinateFlipMass j0 = p := by
    change (∑ mask : MutationMask n,
      if j0 ∈ mask then mutationMaskWeight p mask else 0) = p
    rw [← Finset.sum_filter, ← hfamily]
    rw [Finset.sum_image]
    · simpa [j0] using (leadingOnesExitMaskFamilyWeight_eq p j0)
    · intro a _ha b _hb hab
      exact leadingOnesExitMask_injective j0 hab
  calc
    law.coordinateFlipMass i = law.coordinateFlipMass j0 :=
      law.coordinateFlipMass_eq i j0
    _ = p := hmass0

end ECRuntime
