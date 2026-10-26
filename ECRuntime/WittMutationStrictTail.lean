import ECRuntime.WittMutationCaseC3
import ECRuntime.WittStandardStrictTailDownset
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 45: parameterized C2A strict-tail closure

Stages 42--44 generalized Witt's refined potential, the singleton drift extraction, and
C3 to an arbitrary mutation rate `0 <= p < 1`.  The only unresolved non-singleton
branch is C2A.

The mask geometry developed in Stages 33--37 is independent of the potential and, in
particular, the erase-closed strict family, prefix masses, first-flip decomposition, and
prefix-erasure inequality are already stated for an arbitrary Bernoulli mutation rate.
This module therefore only supplies the pieces that really depend on the parameterized
potential:

* local C2 decomposition for `wittMutationLinearPotential p`;
* elimination of equal-weight C2A masks;
* selected strict-tail bad-mass accounting with parameterized coefficients;
* the ordered envelope
  `g_p(j_r) <= g_p(i) * (1-p)^r`;
* combination with the promoted rate-generic downset theorem.

The result is that C2 is nonnegative for every `0 <= p < 1`.  Hence the only numerical
restriction on the general-rate one-step proof is the Stage-44 C3 envelope.  In
particular, for `p = c/n`, `0 <= c <= 1`, and `n >= 4`, the full parameterized Witt
potential has multiplicative drift rate `p(1-p)^(n-1)`.
-/

/-! ## Localizing C2 for the parameterized potential -/

noncomputable def wittMutationCaseC2AtContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

noncomputable def wittMutationCaseC2AContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

noncomputable def wittMutationCaseC2BContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2BAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

theorem wittMutationCaseC2AtContribution_eq_A_add_B {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittMutationCaseC2AtContribution p w x i =
      wittMutationCaseC2AContribution p w x i +
        wittMutationCaseC2BContribution p w x i := by
  classical
  unfold wittMutationCaseC2AtContribution wittMutationCaseC2AContribution
    wittMutationCaseC2BContribution
  rw [classicalLinearCaseC2AtAcceptedMasks_eq_A_union_B w x i]
  exact Finset.sum_union (classicalLinearCaseC2AAcceptedMasks_disjoint_B w x i)

theorem wittMutationCaseC2BContribution_eq_zero {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    wittMutationCaseC2BContribution p w x i = 0 := by
  unfold wittMutationCaseC2BContribution
  apply Finset.sum_eq_zero
  intro mask hmask
  have hdata := (mem_classicalLinearCaseC2BAcceptedMasks w x i mask).mp hmask
  rw [wittMutationLinearPotential_selected_drop_eq_zero_of_caseC2B
    p w hw hmono x mask i hdata.1]
  ring

theorem wittMutationCaseC2Contribution_eq_accepted {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittMutationCaseC2Contribution p w x =
      ∑ mask ∈ classicalLinearCaseC2AcceptedMasks w x,
        mutationMaskWeight p mask *
          (wittMutationLinearPotential p w x -
            wittMutationLinearPotential p w
              (selectedAfterMask (linearFitness w) x mask)) := by
  classical
  unfold wittMutationCaseC2Contribution classicalLinearCaseC2AcceptedMasks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp [hacc]
  · rw [wittMutationLinearPotential_selected_drop_of_rejects p w x mask hacc]
    simp [hacc]

theorem wittMutationCaseC2Contribution_eq_sum_zeroPositions_at {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittMutationCaseC2Contribution p w x =
      ∑ i ∈ zeroPositions x, wittMutationCaseC2AtContribution p w x i := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))
  have hC2set :
      classicalLinearCaseC2AcceptedMasks w x =
        (Finset.univ : Finset (MutationMask n)).filter (fun mask =>
          IsClassicalLinearCaseC2 x mask ∧
            Accepts (linearFitness w) x (mutateWithMask x mask)) := by
    ext mask
    simp
  have hAtset : ∀ i : Fin n,
      classicalLinearCaseC2AtAcceptedMasks w x i =
        (Finset.univ : Finset (MutationMask n)).filter (fun mask =>
          IsClassicalLinearCaseC2At x mask i ∧
            Accepts (linearFitness w) x (mutateWithMask x mask)) := by
    intro i
    ext mask
    simp
  rw [wittMutationCaseC2Contribution_eq_accepted p w x]
  unfold wittMutationCaseC2AtContribution
  change (∑ mask ∈ classicalLinearCaseC2AcceptedMasks w x, F mask) =
    ∑ i ∈ zeroPositions x,
      ∑ mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i, F mask
  rw [hC2set, Finset.sum_filter]
  calc
    (∑ mask : MutationMask n,
      if IsClassicalLinearCaseC2 x mask ∧
          Accepts (linearFitness w) x (mutateWithMask x mask)
        then F mask else 0) =
        ∑ mask : MutationMask n,
          ∑ i ∈ zeroPositions x,
            if IsClassicalLinearCaseC2At x mask i ∧
                Accepts (linearFitness w) x (mutateWithMask x mask)
              then F mask else 0 := by
          apply Finset.sum_congr rfl
          intro mask hmask
          symm
          simpa only [mem_classicalLinearCaseC2AtAcceptedMasks,
            mem_classicalLinearCaseC2AcceptedMasks] using
            (sum_zeroPositions_caseC2At_indicator_eq_caseC2_indicator
              w x mask (F mask))
    _ = ∑ i ∈ zeroPositions x,
          ∑ mask : MutationMask n,
            if IsClassicalLinearCaseC2At x mask i ∧
                Accepts (linearFitness w) x (mutateWithMask x mask)
              then F mask else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ zeroPositions x,
          ∑ mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i, F mask := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hAtset i, Finset.sum_filter]

theorem wittMutationCaseC2Contribution_eq_sum_zeroPositions_A {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittMutationCaseC2Contribution p w x =
      ∑ i ∈ zeroPositions x, wittMutationCaseC2AContribution p w x i := by
  rw [wittMutationCaseC2Contribution_eq_sum_zeroPositions_at]
  apply Finset.sum_congr rfl
  intro i hi
  rw [wittMutationCaseC2AtContribution_eq_A_add_B,
    wittMutationCaseC2BContribution_eq_zero p w hw hmono x i]
  ring

/-! ## Removing the singleton and equal-weight zero branches -/

noncomputable def wittMutationCaseC2ANonSingletonContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

theorem wittMutationCaseC2AContribution_eq_singleton_add_nonSingleton {n : ℕ}
    {p : ℝ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittMutationCaseC2AContribution p w x i =
      linearSingletonRate n p * wittMutationPotentialWeight p w i +
        wittMutationCaseC2ANonSingletonContribution p w x i := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))
  have hsingle :
      ({i} : MutationMask n) ∈ classicalLinearCaseC2AAcceptedMasks w x i :=
    singleton_mem_classicalLinearCaseC2AAcceptedMasks w hw x i hi
  have hsum := Finset.sum_erase_add
    (classicalLinearCaseC2AAcceptedMasks w x i) F hsingle
  have hF :
      F ({i} : MutationMask n) =
        linearSingletonRate n p * wittMutationPotentialWeight p w i := by
    dsimp [F]
    rw [mutationMaskWeight_singleton,
      wittMutationLinearPotential_selected_single_zero_flip_drop p w hw x i hi]
    rfl
  unfold wittMutationCaseC2AContribution
    wittMutationCaseC2ANonSingletonContribution
    wittStandardCaseC2ANonSingletonAcceptedMasks
  change (∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i, F mask) =
    linearSingletonRate n p * wittMutationPotentialWeight p w i +
      ∑ mask ∈ (classicalLinearCaseC2AAcceptedMasks w x i).erase
        ({i} : MutationMask n), F mask
  rw [← hF]
  simpa only [add_comm] using hsum.symm

noncomputable def wittMutationCaseC2ALocalRemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  wittMutationCaseC2AContribution p w x i -
    linearSingletonRate n p * wittMutationPotentialWeight p w i

theorem wittMutationCaseC2ALocalRemainder_eq_nonSingleton {n : ℕ}
    {p : ℝ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittMutationCaseC2ALocalRemainderContribution p w x i =
      wittMutationCaseC2ANonSingletonContribution p w x i := by
  unfold wittMutationCaseC2ALocalRemainderContribution
  rw [wittMutationCaseC2AContribution_eq_singleton_add_nonSingleton w hw x i hi]
  ring

theorem wittMutationCaseC2RemainderContribution_eq_sum_localA {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittMutationCaseC2RemainderContribution p w x =
      ∑ i ∈ zeroPositions x,
        wittMutationCaseC2ALocalRemainderContribution p w x i := by
  unfold wittMutationCaseC2RemainderContribution
    wittMutationCaseC2ALocalRemainderContribution
  rw [wittMutationCaseC2Contribution_eq_sum_zeroPositions_A p w hw hmono x,
    wittMutationLinearPotential_eq_sum_zeroPositions, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

theorem wittMutationCaseC2RemainderContribution_eq_sum_nonSingletonA {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittMutationCaseC2RemainderContribution p w x =
      ∑ i ∈ zeroPositions x,
        wittMutationCaseC2ANonSingletonContribution p w x i := by
  rw [wittMutationCaseC2RemainderContribution_eq_sum_localA p w hw hmono x]
  apply Finset.sum_congr rfl
  intro i hi
  have hxi : x i = false := (mem_zeroPositions x i).mp hi
  exact wittMutationCaseC2ALocalRemainder_eq_nonSingleton w hw x i hxi

theorem wittMutationLinearPotential_selected_drop_eq_zero_of_caseC2At_equal_bad
    {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i j : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask))
    (hj : j ∈ oneToZeroFlips x mask) (hwji : w j = w i) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  rcases accepted_caseC2At_eq_equalWeight_pair_of_bad_equal
    w hw x mask i j hAt hacc hj hwji with ⟨hone, _hmask⟩
  rw [wittMutationLinearPotential_selected_drop_of_accepts p w x mask hacc,
    flipContribution_sum_eq_flip_sums, hAt, hone]
  simp only [Finset.sum_singleton]
  rw [wittMutationPotentialWeight_eq_of_weight_eq p w hwji]
  ring

noncomputable def wittMutationCaseC2AEqualContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AEqualAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

noncomputable def wittMutationCaseC2AStrictContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

theorem wittMutationCaseC2AEqualContribution_eq_zero {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) :
    wittMutationCaseC2AEqualContribution p w x i = 0 := by
  unfold wittMutationCaseC2AEqualContribution
  apply Finset.sum_eq_zero
  intro mask hmask
  have hdata := (mem_wittStandardCaseC2AEqualAcceptedMasks w x i mask).mp hmask
  have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
    w x i mask).mp hdata.1
  have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
  rcases hdata.2 with ⟨j, hj, hwji⟩
  rw [wittMutationLinearPotential_selected_drop_eq_zero_of_caseC2At_equal_bad
    p w hw x mask i j hAdata.1.1 hAdata.2 hj hwji]
  ring

theorem wittMutationCaseC2ANonSingletonContribution_eq_strict {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) (i : Fin n) :
    wittMutationCaseC2ANonSingletonContribution p w x i =
      wittMutationCaseC2AStrictContribution p w x i := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))
  unfold wittMutationCaseC2ANonSingletonContribution
    wittMutationCaseC2AStrictContribution
  change (∑ mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i, F mask) =
    ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i, F mask
  rw [wittStandardCaseC2ANonSingletonAcceptedMasks_eq_equal_union_strict
    w hmono x i]
  rw [Finset.sum_union (wittStandardCaseC2AEqualAcceptedMasks_disjoint_strict
    w x i)]
  have heq :
      (∑ mask ∈ wittStandardCaseC2AEqualAcceptedMasks w x i, F mask) = 0 := by
    simpa only [F, wittMutationCaseC2AEqualContribution] using
      wittMutationCaseC2AEqualContribution_eq_zero p w hw x i
  rw [heq, zero_add]

theorem wittMutationCaseC2RemainderContribution_eq_sum_strictA {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittMutationCaseC2RemainderContribution p w x =
      ∑ i ∈ zeroPositions x, wittMutationCaseC2AStrictContribution p w x i := by
  rw [wittMutationCaseC2RemainderContribution_eq_sum_nonSingletonA
    p w hw hmono x]
  apply Finset.sum_congr rfl
  intro i hi
  exact wittMutationCaseC2ANonSingletonContribution_eq_strict
    p w hw hmono x i

/-! ## Parameterized strict-tail bad mass -/

noncomputable def wittMutationCaseC2AStrictBadMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (∑ j ∈ oneToZeroFlips x mask, wittMutationPotentialWeight p w j)

theorem wittMutationLinearPotential_selected_drop_eq_good_sub_bad_of_strictC2A
    {n : ℕ} (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) =
      wittMutationPotentialWeight p w i -
        (∑ j ∈ oneToZeroFlips x mask, wittMutationPotentialWeight p w j) := by
  have hstrict := (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hmask
  have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
    w x i mask).mp hstrict.1
  have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
  rw [wittMutationLinearPotential_selected_drop_of_accepts
    p w x mask hAdata.2, flipContribution_sum_eq_flip_sums, hAdata.1.1]
  simp

theorem wittMutationCaseC2AStrictContribution_eq_goodMass_sub_badMass
    {n : ℕ} (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittMutationCaseC2AStrictContribution p w x i =
      wittMutationPotentialWeight p w i *
          wittStandardCaseC2AStrictAcceptedMass p w x i -
        wittMutationCaseC2AStrictBadMass p w x i := by
  unfold wittMutationCaseC2AStrictContribution
    wittStandardCaseC2AStrictAcceptedMass
    wittMutationCaseC2AStrictBadMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  rw [wittMutationLinearPotential_selected_drop_eq_good_sub_bad_of_strictC2A
    p w x i mask hmask]
  ring

theorem wittMutationCaseC2AStrictBadMass_eq_sum_coordinate_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittMutationCaseC2AStrictBadMass p w x i =
      ∑ j : Fin n,
        if x j = true then
          wittMutationPotentialWeight p w j *
            wittStandardCaseC2AStrictFlipAtMass p w x i j
        else 0 := by
  classical
  unfold wittMutationCaseC2AStrictBadMass
  simp_rw [oneToZeroFlips, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hxj : x j = true
  · rw [if_pos hxj]
    unfold wittStandardCaseC2AStrictFlipAtMass
      wittStandardCaseC2AStrictAcceptedWithFlipAt
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro mask hmask
    by_cases hjm : j ∈ mask <;> simp [hxj, hjm, mul_comm]
  · rw [if_neg hxj]
    apply Finset.sum_eq_zero
    intro mask hmask
    simp [hxj]

theorem wittMutationCaseC2AStrictBadMass_eq_sum_tail_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittMutationCaseC2AStrictBadMass p w x i =
      ∑ j ∈ wittStandardStrictTailIndices w x i,
        wittMutationPotentialWeight p w j *
          wittStandardCaseC2AStrictFlipAtMass p w x i j := by
  rw [wittMutationCaseC2AStrictBadMass_eq_sum_coordinate_flipMass]
  unfold wittStandardStrictTailIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hxj : x j = true
  · by_cases hji : w j < w i
    · simp [hxj, hji]
    · have hzero := wittStandardCaseC2AStrictFlipAtMass_eq_zero_of_not_lt
        p w x i j hxj hji
      simp [hxj, hji, hzero]
  · simp [hxj]

theorem wittMutationCaseC2AStrictBadMass_eq_sum_tail_closureFlipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (hi : x i = false) :
    wittMutationCaseC2AStrictBadMass p w x i =
      ∑ j ∈ wittStandardStrictTailIndices w x i,
        wittMutationPotentialWeight p w j *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by
  rw [wittMutationCaseC2AStrictBadMass_eq_sum_tail_flipMass]
  apply Finset.sum_congr rfl
  intro j hj
  have hjData := (mem_wittStandardStrictTailIndices w x i j).mp hj
  rw [wittStandardCaseC2AStrictFlipAtMass_eq_closureFlipAtMass
    p w x i j hi hjData.1]

theorem wittMutationCaseC2AStrictBadMass_eq_sum_ordered_closureFlipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (hi : x i = false) :
    wittMutationCaseC2AStrictBadMass p w x i =
      ∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittMutationPotentialWeight p w
            (wittStandardStrictTailCoordinate w x i r) *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (wittStandardStrictTailCoordinate w x i r) := by
  rw [wittMutationCaseC2AStrictBadMass_eq_sum_tail_closureFlipMass
    p w x i hi]
  let T : Finset (Fin n) := wittStandardStrictTailIndices w x i
  have himage :
      Finset.image (fun r : Fin T.card => T.orderEmbOfFin rfl r) Finset.univ = T :=
    T.image_orderEmbOfFin_univ rfl
  calc
    (∑ j ∈ wittStandardStrictTailIndices w x i,
      wittMutationPotentialWeight p w j *
        wittStandardCaseC2AStrictClosureFlipAtMass p w x i j) =
      ∑ j ∈ Finset.image (fun r : Fin T.card => T.orderEmbOfFin rfl r) Finset.univ,
        wittMutationPotentialWeight p w j *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by
        rw [himage]
    _ = ∑ r : Fin T.card,
        wittMutationPotentialWeight p w (T.orderEmbOfFin rfl r) *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (T.orderEmbOfFin rfl r) := by
      rw [Finset.sum_image (by
        intro a _ b _ hab
        exact (T.orderEmbOfFin rfl).injective hab)]
    _ = ∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittMutationPotentialWeight p w
            (wittStandardStrictTailCoordinate w x i r) *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (wittStandardStrictTailCoordinate w x i r) := by
      rfl

/-! ## Parameterized ordered envelope and downset closure -/

theorem wittMutationStrictTail_ordered_weight_le {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittMutationPotentialWeight p w
        (wittStandardStrictTailCoordinate w x i r) ≤
      wittMutationPotentialWeight p w i * (1 - p) ^ r.val := by
  have hgap :
      wittStandardExponent w (wittStandardStrictTailCoordinate w x i r) + r.val ≤
        wittStandardExponent w i := by
    simpa [wittStandardStrictTailCoordinate] using
      wittStandardExponent_add_strictTailRank_le w hmono x i r
  have hpow :
      wittMutationBase p ^
          (wittStandardExponent w (wittStandardStrictTailCoordinate w x i r) + r.val) ≤
        wittMutationBase p ^ wittStandardExponent w i :=
    (pow_right_mono₀ (one_le_wittMutationBase hp0 hp1)) hgap
  have hsurv : 0 ≤ 1 - p := (wittMutation_survival_pos hp1).le
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hsurv r.val)
  have hcancel := wittMutationBase_pow_mul_survival_pow hp1 r.val
  simpa [wittMutationPotentialWeight, pow_add, mul_assoc, hcancel] using hmul

theorem wittMutationCaseC2AStrictBadMass_le_good_mul_strictAcceptedMass {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittMutationCaseC2AStrictBadMass p w x i ≤
      wittMutationPotentialWeight p w i *
        wittStandardCaseC2AStrictAcceptedMass p w x i := by
  rw [wittMutationCaseC2AStrictBadMass_eq_sum_ordered_closureFlipMass
    p w x i hi]
  calc
    (∑ r : Fin (wittStandardStrictTailIndices w x i).card,
      wittMutationPotentialWeight p w
          (wittStandardStrictTailCoordinate w x i r) *
        wittStandardCaseC2AStrictClosureFlipAtMass p w x i
          (wittStandardStrictTailCoordinate w x i r)) ≤
      ∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittMutationPotentialWeight p w i *
          wittStandardCaseC2AStrictFirstFlipMass p w x i r := by
      apply Finset.sum_le_sum
      intro r hr
      have hweight := wittMutationStrictTail_ordered_weight_le
        hp0 hp1 w hmono x i r
      have hmassNonneg :
          0 ≤ wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (wittStandardStrictTailCoordinate w x i r) := by
        unfold wittStandardCaseC2AStrictClosureFlipAtMass
        apply Finset.sum_nonneg
        intro mask hmask
        exact mutationMaskWeight_nonneg hp0 hp1.le mask
      have hprefix :=
        standardSurvival_pow_mul_wittStandardCaseC2AStrictClosureFlipAtMass_le_firstFlipMass
          hp0 hp1.le w hw x i r
      have hgoodNonneg := (wittMutationPotentialWeight_pos hp0 hp1 w i).le
      calc
        wittMutationPotentialWeight p w (wittStandardStrictTailCoordinate w x i r) *
            wittStandardCaseC2AStrictClosureFlipAtMass p w x i
              (wittStandardStrictTailCoordinate w x i r) ≤
          (wittMutationPotentialWeight p w i * (1 - p) ^ r.val) *
            wittStandardCaseC2AStrictClosureFlipAtMass p w x i
              (wittStandardStrictTailCoordinate w x i r) :=
          mul_le_mul_of_nonneg_right hweight hmassNonneg
        _ = wittMutationPotentialWeight p w i *
            ((1 - p) ^ r.val *
              wittStandardCaseC2AStrictClosureFlipAtMass p w x i
                (wittStandardStrictTailCoordinate w x i r)) := by ring
        _ ≤ wittMutationPotentialWeight p w i *
            wittStandardCaseC2AStrictFirstFlipMass p w x i r :=
          mul_le_mul_of_nonneg_left hprefix hgoodNonneg
    _ = wittMutationPotentialWeight p w i *
        (∑ r : Fin (wittStandardStrictTailIndices w x i).card,
          wittStandardCaseC2AStrictFirstFlipMass p w x i r) := by
      rw [Finset.mul_sum]
    _ = wittMutationPotentialWeight p w i *
        wittStandardCaseC2AStrictAcceptedMass p w x i := by
      rw [sum_wittStandardCaseC2AStrictFirstFlipMass_eq_strictAcceptedMass
        p w hw x i hi]

theorem wittMutationCaseC2AStrictContribution_nonneg {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    0 ≤ wittMutationCaseC2AStrictContribution p w x i := by
  rw [wittMutationCaseC2AStrictContribution_eq_goodMass_sub_badMass]
  exact sub_nonneg.mpr
    (wittMutationCaseC2AStrictBadMass_le_good_mul_strictAcceptedMass
      hp0 hp1 w hw hmono x i hi)

/-- C2 is nonnegative for every genuine subunit mutation rate. -/
theorem wittMutation_hasCaseC2RemainderNonnegativity {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasWittMutationCaseC2RemainderNonnegativity p w := by
  intro x
  rw [wittMutationCaseC2RemainderContribution_eq_sum_strictA p w hw hmono x]
  apply Finset.sum_nonneg
  intro i hi
  exact wittMutationCaseC2AStrictContribution_nonneg
    hp0 hp1 w hw hmono x i ((mem_zeroPositions x i).mp hi)

/-! ## Closing the general one-step theorem -/

/-- Under the exact Stage-44 C3 envelope, all non-singleton parameterized-Witt drift is
nonnegative. -/
theorem wittMutation_hasRemainderNonnegativity_of_c3Envelope {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (henv : WittMutationC3EnvelopeCondition p n) :
    HasWittMutationRemainderNonnegativity p w := by
  exact hasWittMutationRemainderNonnegativity_of_caseC2_of_envelope
    hp0 hp1 w hw hmono henv
      (wittMutation_hasCaseC2RemainderNonnegativity hp0 hp1 w hw hmono)

/-- Multiplicative drift at the exact singleton rate under the finite C3 envelope. -/
theorem wittMutation_hasMultiplicativeDriftLowerBound_of_c3Envelope {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (henv : WittMutationC3EnvelopeCondition p n) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition p (linearFitness w))
      (wittMutationLinearPotential p w)
      (linearSingletonRate n p) := by
  apply wittMutation_hasMultiplicativeDriftLowerBound_of_remainder_nonnegative
    w hw
  exact wittMutation_hasRemainderNonnegativity_of_c3Envelope
    hp0 hp1 w hw hmono henv

/-- Concrete scaled-rate one-step theorem on the first formally closed interval
`0 <= c <= 1`. -/
theorem wittMutation_hasMultiplicativeDriftLowerBound_scaled_of_le_one {n : ℕ}
    (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (scaledMutationRate c n) (linearFitness w))
      (wittMutationLinearPotential (scaledMutationRate c n) w)
      (linearSingletonRate n (scaledMutationRate c n)) := by
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0 hc1
  have hp1 : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt hp_le (standardMutationRate_lt_one (by omega : 2 ≤ n))
  exact wittMutation_hasMultiplicativeDriftLowerBound_of_c3Envelope
    (scaledMutationRate_nonneg hc0) hp1 w hw hmono
    (wittMutationC3EnvelopeCondition_scaled_of_le_one hn hc0 hc1)

end ECRuntime
