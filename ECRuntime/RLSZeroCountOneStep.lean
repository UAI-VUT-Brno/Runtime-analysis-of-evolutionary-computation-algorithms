import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-! Provisional public Stage 124: active proof candidate. Exact one-step drift of the number of
zeros under one-bit RLS; this is the missing eigenfunction for Stage 115. -/

/-- The outcome of flipping one prescribed coordinate under elitist OneMax
    is exactly the initial zero count or one less.  This is the local
    combinatorial identity needed for the exact Stage-124 one-step mean. -/
private theorem stage124_selected_zeroCount_singleton
    {n : Nat} (x : BitString n) (i : Fin n) :
    zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
      if x i = false then zeroCount x - 1 else zeroCount x := by
  by_cases hxi : x i = false
  · have hacc : Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      exact_mod_cast Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi)
    rw [selectedAfterMask, elitistSelect_of_accepts _ _ _ hacc, if_pos hxi]
    have hcount := zeroCount_mutate_single_of_false x i hxi
    omega
  · have hxi' : x i = true := by
      cases hi : x i <;> simp_all
    have hrej : ¬ Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      have hcount := oneCount_mutate_single_of_true x i hxi'
      have hdrop : oneCount (mutateWithMask x ({i} : MutationMask n)) <
          oneCount x := by omega
      exact not_le_of_gt (by exact_mod_cast hdrop :
        (oneCount (mutateWithMask x ({i} : MutationMask n)) : Real) <
          (oneCount x : Real))
    rw [selectedAfterMask, elitistSelect_of_rejects _ _ _ hrej, if_neg hxi]

/-- RLS on OneMax decreases the expected zero count by a fraction `1/n`
in every state, including the optimum. -/
theorem proposed_rlsOneMax_expectedZeroCount_oneStep
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real)) x =
        (1 - 1 / (n : Real)) * (zeroCount x : Real) := by
  exact candidate_rlsOneMax_expectedZeroCount_exact hn x

end ECRuntime
