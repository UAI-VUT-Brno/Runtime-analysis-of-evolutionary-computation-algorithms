import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.OneMax
import ECRuntime.FitnessLevel
import Mathlib

namespace ECRuntime

/-! PROVISIONAL PUBLIC Stage 122 proposal: isolate the one-step harmonic identity
used by the exact RLS coupon-collector Bellman theorem. Proof work is authorized by the user; independent candidate gate applies. -/

/-- A single RLS step removes exactly one zero when it selects a zero
coordinate; otherwise elitist OneMax rejects the move. This isolates the
coordinatewise combinatorics needed by the harmonic Bellman equality. -/
private theorem stage122_selected_zeroCount_singleton
    {n : Nat} (x : BitString n) (i : Fin n) :
    zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
      if x i = false then zeroCount x - 1 else zeroCount x := by
  by_cases hxi : x i = false
  · have hacc : Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      exact_mod_cast Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi)
    rw [selectedAfterMask,
      elitistSelect_of_accepts _ _ _ hacc, if_pos hxi]
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
    rw [selectedAfterMask,
      elitistSelect_of_rejects _ _ _ hrej, if_neg hxi]

/-- Exact harmonic successor identity, as opposed to the existing
    monotone lower bound. -/
private theorem stage122_harmonicReal_succ (k : Nat) :
    harmonicReal (k + 1) = harmonicReal k + ((k + 1 : Nat) : Real)⁻¹ := by
  simp [harmonicReal, harmonic_succ]

/-- The scaled harmonic potential decreases by one in conditional
expectation at every nonoptimal OneMax state under one-bit RLS. At the
optimum it is zero. This is the missing local certificate for Stage 109. -/
theorem proposed_oneMaxRLS_harmonic_one_step
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n =>
        (n : Real) * harmonicReal (zeroCount y)) x =
      if zeroCount x = 0 then 0
      else (n : Real) * harmonicReal (zeroCount x) - 1 := by
  exact candidate_rlsOneMax_harmonic_one_step hn x

end ECRuntime
