import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LinearPotential
import ECRuntime.OneMax
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Provisional public shared proof support for approved candidates 109/114/115.
Positive linear weights guarantee that each singleton flip has the same
accept/reject decision as OneMax. Consequently the transition matrices
are literally equal; no unproved sorting of weight coordinates is used.
-/

/-- Positive linear and OneMax selection agree for a specified singleton. -/
theorem candidate_rls_selected_singleton_eq_oneMax
    {n : Nat} (w : Fin n → Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) :
    selectedAfterMask (linearFitness w) x ({i} : MutationMask n) =
      selectedAfterMask oneMaxReal x ({i} : MutationMask n) := by
  classical
  let z : BitString n := mutateWithMask x ({i} : MutationMask n)
  by_cases hxi : x i = false
  · have hl : Accepts (linearFitness w) x z := by
      exact le_of_lt (linearFitness_single_zero_flip_improves w hw x i hxi)
    have hm : Accepts oneMaxReal x z := by
      unfold Accepts oneMaxReal
      exact_mod_cast (Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi))
    simp [selectedAfterMask, z, elitistSelect_of_accepts _ _ _ hl,
      elitistSelect_of_accepts _ _ _ hm]
  · have hxi' : x i = true := by cases h : x i <;> simp_all
    have hzi : z i = false := by simp [z, hxi']
    have hback : mutateWithMask z ({i} : MutationMask n) = x := by
      simp [z]
    have hdecrease : linearFitness w z < linearFitness w x := by
      simpa [hback] using
        (linearFitness_single_zero_flip_improves w hw z i hzi)
    have hl : ¬ Accepts (linearFitness w) x z := not_le_of_gt hdecrease
    have hm : ¬ Accepts oneMaxReal x z := by
      unfold Accepts oneMaxReal
      have hcount := oneCount_mutate_single_of_true x i hxi'
      have hnat : oneCount z < oneCount x := by
        dsimp [z]
        omega
      exact not_le_of_gt
        (by exact_mod_cast hnat : (oneCount z : Real) < oneCount x)
    simp [selectedAfterMask, z, elitistSelect_of_rejects _ _ _ hl,
      elitistSelect_of_rejects _ _ _ hm]

/-- Exact equality of the RLS transition matrices, for all states. -/
theorem candidate_rls_linear_transition_eq_oneMax
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
      (linearFitness w) =
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
      oneMaxReal := by
  classical
  funext x y
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  change (∑ mask : MutationMask n,
    if selectedAfterMask (linearFitness w) x mask = y
    then law.weight mask else 0) =
    ∑ mask : MutationMask n,
      if selectedAfterMask oneMaxReal x mask = y
      then law.weight mask else 0
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hc : mask.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    subst mask
    rw [candidate_rls_selected_singleton_eq_oneMax w hw x i]
  · have hzero : law.weight mask = 0 := by
      dsimp [law, StaticUnaryUnbiasedMutation.uniformOneBitLaw]
      simp [hc]
    simp [hzero]

end ECRuntime
