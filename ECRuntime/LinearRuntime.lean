import ECRuntime.MultiplicativeDrift
import ECRuntime.LinearPotential
import ECRuntime.LinearObjectiveRuntime
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-- The zero level of the classical rank potential. -/
def rankLinearTarget (n : ℕ) : Set (BitString n) :=
  realPotentialTarget (rankLinearPotential (n := n))

/-- Membership in the zero level of the real-valued rank potential is decidable classically. -/
noncomputable instance instDecidablePredRankLinearTarget (n : ℕ) :
    DecidablePred (fun x : BitString n => x ∈ rankLinearTarget n) := by
  classical
  intro x
  change Decidable (rankLinearPotential (n := n) x = 0)
  infer_instance

/-- In positive dimension the rank-potential target is exactly the all-one optimum. -/
theorem rankLinearTarget_eq_singleton {n : ℕ} (hn : 0 < n) :
    rankLinearTarget n = ({allOnes n} : Set (BitString n)) := by
  ext x
  simp [rankLinearTarget, realPotentialTarget, rankLinearPotential_eq_zero_iff hn]

/-- Every state outside the rank target has potential at least one. -/
theorem one_le_rankLinearPotential_of_not_target {n : ℕ}
    (hn : 0 < n) (x : BitString n) (hx : x ∉ rankLinearTarget n) :
    1 ≤ rankLinearPotential x := by
  have hxne : x ≠ allOnes n := by
    intro h
    apply hx
    rw [rankLinearTarget_eq_singleton hn]
    simp [h]
  exact one_le_rankLinearPotential_of_ne_allOnes hn x hxne

/-- The drift rate from Lemma 5 of Doerr--Johannsen--Winzen, in our convention. -/
noncomputable def classicalLinearDriftRate (n : ℕ) : ℝ :=
  (4 * Real.exp 1 * (n : ℝ))⁻¹

/-- The classical linear-function drift rate is positive in positive dimension. -/
theorem classicalLinearDriftRate_pos {n : ℕ} (hn : 0 < n) :
    0 < classicalLinearDriftRate n := by
  unfold classicalLinearDriftRate
  apply inv_pos.mpr
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) (by exact_mod_cast hn)

/-- Standard mutation is a valid probability in dimension at least two. -/
theorem standardMutationRate_mem_unitInterval_linear {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ standardMutationRate n ∧ standardMutationRate n ≤ 1 := by
  have hnpos : 0 < n := by omega
  have hp0 : 0 < standardMutationRate n := by
    rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)]
    exact inv_pos.mpr (by exact_mod_cast hnpos)
  have hp1 : standardMutationRate n < 1 := by
    rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)]
    have hn1 : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    exact inv_lt_one_of_one_lt₀ hn1
  exact ⟨hp0.le, hp1.le⟩


/-- Standard mutation instantiation of the coefficient-sensitive objective-error theorem. -/
theorem linearObjectiveError_standard_runtimeSup_le
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (wmin : ℝ)
    (hwmin : 0 < wmin) (hwl : ∀ i, wmin ≤ w i)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (linearObjectiveErrorTarget w) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          (linearSingletonRate n (standardMutationRate n))
          wmin (linearErrorPotential w) x) := by
  have hnpos : 0 < n := by omega
  have hp0 : 0 < standardMutationRate n := by
    rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)]
    exact inv_pos.mpr (by exact_mod_cast hnpos)
  have hp1 : standardMutationRate n < 1 := by
    rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)]
    have hn1 : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    exact inv_lt_one_of_one_lt₀ hn1
  exact linearObjectiveError_runtimeSup_le hp0 hp1 w wmin hwmin hwl x


/-- One-step rank-potential drift written directly as a mutation-mask expectation. -/
theorem rankLinear_drift_eq_mask_sum {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (rankLinearPotential (n := n)) x =
      ∑ mask : MutationMask n,
        mutationMaskWeight p mask *
          (rankLinearPotential x -
            rankLinearPotential (selectedAfterMask (linearFitness w) x mask)) := by
  exact onePlusOneTransition_drift_eq_mask_sum
    p (linearFitness w) (rankLinearPotential (n := n)) x

/--
The simple events that flip one currently-zero bit and no other bit contribute exactly
`p(1-p)^(n-1) * g(x)` to the raw rank-potential drift sum.  The difficult part of the
classical linear-functions proof is therefore entirely in controlling the remaining
accepted multi-bit masks.
-/
theorem rankLinear_zeroSingleton_contribution_eq
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ zeroSingletonMasks x,
      mutationMaskWeight p mask *
        (rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) =
      linearSingletonRate n p * rankLinearPotential x := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))
  have hcoord :
      ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) =
        linearSingletonRate n p * rankLinearPotential x := by
    rw [rankLinearPotential_eq_sum_zeroPositions, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hzero : x i = false := (mem_zeroPositions x i).mp hi
    dsimp [F]
    rw [mutationMaskWeight_singleton,
      rankLinearPotential_selected_single_zero_flip_drop w hw x i hzero]
    rfl
  calc
    (∑ mask ∈ zeroSingletonMasks x,
      mutationMaskWeight p mask *
        (rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) =
        ∑ mask ∈ zeroSingletonMasks x, F mask := by rfl
    _ = ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) := by
      unfold zeroSingletonMasks
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Finset.singleton_injective hab
    _ = linearSingletonRate n p * rankLinearPotential x := hcoord

/-- Finite set of mutation masks in classical case C1. -/
noncomputable def classicalLinearCaseC1Masks {n : ℕ} (x : BitString n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (IsClassicalLinearCaseC1 x)

/-- Finite set of mutation masks in classical case C2. -/
noncomputable def classicalLinearCaseC2Masks {n : ℕ} (x : BitString n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (IsClassicalLinearCaseC2 x)

/-- Finite set of mutation masks in classical case C3. -/
noncomputable def classicalLinearCaseC3Masks {n : ℕ} (x : BitString n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (IsClassicalLinearCaseC3 x)

@[simp] theorem mem_classicalLinearCaseC1Masks {n : ℕ}
    (x : BitString n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC1Masks x ↔ IsClassicalLinearCaseC1 x mask := by
  classical
  simp [classicalLinearCaseC1Masks]

@[simp] theorem mem_classicalLinearCaseC2Masks {n : ℕ}
    (x : BitString n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2Masks x ↔ IsClassicalLinearCaseC2 x mask := by
  classical
  simp [classicalLinearCaseC2Masks]

@[simp] theorem mem_classicalLinearCaseC3Masks {n : ℕ}
    (x : BitString n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC3Masks x ↔ IsClassicalLinearCaseC3 x mask := by
  classical
  simp [classicalLinearCaseC3Masks]


/-- Accepted masks in C2.  Rejected C2 masks contribute zero after elitist selection. -/
noncomputable def classicalLinearCaseC2AcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) : Finset (MutationMask n) := by
  classical
  exact (classicalLinearCaseC2Masks x).filter
    (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask))

@[simp] theorem mem_classicalLinearCaseC2AcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2AcceptedMasks w x ↔
      IsClassicalLinearCaseC2 x mask ∧
        Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  simp [classicalLinearCaseC2AcceptedMasks]

/-- Accepted C2 masks whose unique improving coordinate is `i`. -/
noncomputable def classicalLinearCaseC2AtAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (fun mask =>
    IsClassicalLinearCaseC2At x mask i ∧
      Accepts (linearFitness w) x (mutateWithMask x mask))

/-- Accepted `A_i` masks. -/
noncomputable def classicalLinearCaseC2AAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (fun mask =>
    IsClassicalLinearCaseC2A x mask i ∧
      Accepts (linearFitness w) x (mutateWithMask x mask))

/-- Accepted `B_i` masks. -/
noncomputable def classicalLinearCaseC2BAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (fun mask =>
    IsClassicalLinearCaseC2B x mask i ∧
      Accepts (linearFitness w) x (mutateWithMask x mask))

@[simp] theorem mem_classicalLinearCaseC2AtAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i ↔
      IsClassicalLinearCaseC2At x mask i ∧
        Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  simp [classicalLinearCaseC2AtAcceptedMasks]

@[simp] theorem mem_classicalLinearCaseC2AAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2AAcceptedMasks w x i ↔
      IsClassicalLinearCaseC2A x mask i ∧
        Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  simp [classicalLinearCaseC2AAcceptedMasks]

@[simp] theorem mem_classicalLinearCaseC2BAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2BAcceptedMasks w x i ↔
      IsClassicalLinearCaseC2B x mask i ∧
        Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  simp [classicalLinearCaseC2BAcceptedMasks]

/-- For a fixed improving coordinate, accepted C2 masks split into `A_i` and `B_i`. -/
theorem classicalLinearCaseC2AtAcceptedMasks_eq_A_union_B {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    classicalLinearCaseC2AtAcceptedMasks w x i =
      classicalLinearCaseC2AAcceptedMasks w x i ∪
        classicalLinearCaseC2BAcceptedMasks w x i := by
  classical
  ext mask
  constructor
  · intro hmask
    have hdata := (mem_classicalLinearCaseC2AtAcceptedMasks w x i mask).mp hmask
    rcases classicalLinearCaseC2A_or_C2B x mask i hdata.1 with hA | hB
    · exact Finset.mem_union.mpr (Or.inl
        ((mem_classicalLinearCaseC2AAcceptedMasks w x i mask).2 ⟨hA, hdata.2⟩))
    · exact Finset.mem_union.mpr (Or.inr
        ((mem_classicalLinearCaseC2BAcceptedMasks w x i mask).2 ⟨hB, hdata.2⟩))
  · intro hmask
    rcases Finset.mem_union.mp hmask with hA | hB
    · have hdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hA
      exact (mem_classicalLinearCaseC2AtAcceptedMasks w x i mask).2 ⟨hdata.1.1, hdata.2⟩
    · have hdata := (mem_classicalLinearCaseC2BAcceptedMasks w x i mask).mp hB
      exact (mem_classicalLinearCaseC2AtAcceptedMasks w x i mask).2 ⟨hdata.1.1, hdata.2⟩

/-- Erasing a worsening flip from an accepted `A_i` mask preserves accepted `A_i`. -/
theorem erase_oneToZero_mem_classicalLinearCaseC2AAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n) (j : Fin n)
    (hmask : mask ∈ classicalLinearCaseC2AAcceptedMasks w x i)
    (hj : j ∈ oneToZeroFlips x mask) :
    mask.erase j ∈ classicalLinearCaseC2AAcceptedMasks w x i := by
  have hdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hmask
  have hjData := (mem_oneToZeroFlips x mask j).mp hj
  apply (mem_classicalLinearCaseC2AAcceptedMasks w x i (mask.erase j)).2
  exact ⟨
    classicalLinearCaseC2A_erase_oneToZero x mask i j hdata.1 hj,
    accepts_erase_oneToZero_of_accepts w hw x mask j hjData.1 hjData.2 hdata.2
  ⟩

/-- The singleton improvement `{i}` is an accepted `A_i` event whenever `x i = false`. -/
theorem singleton_mem_classicalLinearCaseC2AAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    ({i} : MutationMask n) ∈ classicalLinearCaseC2AAcceptedMasks w x i := by
  apply (mem_classicalLinearCaseC2AAcceptedMasks w x i ({i} : MutationMask n)).2
  have hC2 := singleton_zero_is_classicalLinearCaseC2 x i hi
  have hiPos : i ∈ zeroToOneFlips x ({i} : MutationMask n) := by
    simp [zeroToOneFlips, hi]
  have hAt := classicalLinearCaseC2At_of_caseC2_of_mem x ({i} : MutationMask n) i hC2 hiPos
  have hA : IsClassicalLinearCaseC2A x ({i} : MutationMask n) i := by
    refine ⟨hAt, ?_⟩
    intro j hj
    have hjMask : j ∈ ({i} : MutationMask n) :=
      ((mem_oneToZeroFlips x ({i} : MutationMask n) j).mp hj).1
    have hji : j = i := by
      simpa using hjMask
    simp [hji]
  have hacc : Accepts (linearFitness w) x (mutateWithMask x ({i} : MutationMask n)) :=
    le_of_lt (linearFitness_single_zero_flip_improves w hw x i hi)
  exact ⟨hA, hacc⟩

/-- Accepted `A_i` masks that flip a specified coordinate `j`. -/
noncomputable def classicalLinearCaseC2AAcceptedWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : Finset (MutationMask n) := by
  classical
  exact (classicalLinearCaseC2AAcceptedMasks w x i).filter (fun mask => j ∈ mask)

/-- Accepted `A_i` masks that do not flip a specified coordinate `j`. -/
noncomputable def classicalLinearCaseC2AAcceptedWithoutFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : Finset (MutationMask n) := by
  classical
  exact (classicalLinearCaseC2AAcceptedMasks w x i).filter (fun mask => j ∉ mask)

@[simp] theorem mem_classicalLinearCaseC2AAcceptedWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2AAcceptedWithFlipAt w x i j ↔
      mask ∈ classicalLinearCaseC2AAcceptedMasks w x i ∧ j ∈ mask := by
  classical
  simp [classicalLinearCaseC2AAcceptedWithFlipAt]

@[simp] theorem mem_classicalLinearCaseC2AAcceptedWithoutFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC2AAcceptedWithoutFlipAt w x i j ↔
      mask ∈ classicalLinearCaseC2AAcceptedMasks w x i ∧ j ∉ mask := by
  classical
  simp [classicalLinearCaseC2AAcceptedWithoutFlipAt]

/-- Total mutation mass of accepted `A_i` masks. -/
noncomputable def rankLinearCaseC2AAcceptedMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i, mutationMaskWeight p mask

/-- Accepted `A_i` mass among masks that flip coordinate `j`. -/
noncomputable def rankLinearCaseC2AFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedWithFlipAt w x i j, mutationMaskWeight p mask

/-- Accepted `A_i` mass among masks that do not flip coordinate `j`. -/
noncomputable def rankLinearCaseC2AWithoutFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedWithoutFlipAt w x i j, mutationMaskWeight p mask

/-- Accepted `A_i` mass partitions according to whether coordinate `j` flips. -/
theorem rankLinearCaseC2AAcceptedMass_eq_flipAt_add_withoutFlipAt {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) :
    rankLinearCaseC2AAcceptedMass p w x i =
      rankLinearCaseC2AFlipAtMass p w x i j +
        rankLinearCaseC2AWithoutFlipAtMass p w x i j := by
  classical
  unfold rankLinearCaseC2AAcceptedMass rankLinearCaseC2AFlipAtMass
    rankLinearCaseC2AWithoutFlipAtMass
    classicalLinearCaseC2AAcceptedWithFlipAt classicalLinearCaseC2AAcceptedWithoutFlipAt
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hj : j ∈ mask <;> simp [hj]

/--
Erase pairing for `A_i`: conditioning on accepted `A_i` cannot increase the marginal
flip mass of a currently-correct coordinate `j`.
-/
theorem one_sub_p_mul_rankLinearCaseC2AFlipAtMass_le {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i j : Fin n) (hxj : x j = true) :
    (1 - p) * rankLinearCaseC2AFlipAtMass p w x i j ≤
      p * rankLinearCaseC2AWithoutFlipAtMass p w x i j := by
  classical
  unfold rankLinearCaseC2AFlipAtMass rankLinearCaseC2AWithoutFlipAtMass
  rw [Finset.mul_sum, Finset.mul_sum]
  have herase_inj :
      Set.InjOn (fun mask : MutationMask n => mask.erase j)
        ↑(classicalLinearCaseC2AAcceptedWithFlipAt w x i j) := by
    intro a ha b hb hab
    have hja : j ∈ a :=
      ((mem_classicalLinearCaseC2AAcceptedWithFlipAt w x i j a).mp ha).2
    have hjb : j ∈ b :=
      ((mem_classicalLinearCaseC2AAcceptedWithFlipAt w x i j b).mp hb).2
    have hab' : a.erase j = b.erase j := by
      simpa using hab
    calc
      a = insert j (a.erase j) := (Finset.insert_erase hja).symm
      _ = insert j (b.erase j) := by rw [hab']
      _ = b := Finset.insert_erase hjb
  have himage_subset :
      (classicalLinearCaseC2AAcceptedWithFlipAt w x i j).image
          (fun mask : MutationMask n => mask.erase j) ⊆
        classicalLinearCaseC2AAcceptedWithoutFlipAt w x i j := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨mask, hmask, rfl⟩
    have hmaskData :=
      (mem_classicalLinearCaseC2AAcceptedWithFlipAt w x i j mask).mp hmask
    apply (mem_classicalLinearCaseC2AAcceptedWithoutFlipAt w x i j (mask.erase j)).2
    have hjbad : j ∈ oneToZeroFlips x mask :=
      (mem_oneToZeroFlips x mask j).2 ⟨hmaskData.2, hxj⟩
    exact ⟨erase_oneToZero_mem_classicalLinearCaseC2AAcceptedMasks
      w hw x i mask j hmaskData.1 hjbad, by simp⟩
  calc
    (∑ mask ∈ classicalLinearCaseC2AAcceptedWithFlipAt w x i j,
        (1 - p) * mutationMaskWeight p mask) =
      ∑ mask ∈ classicalLinearCaseC2AAcceptedWithFlipAt w x i j,
        p * mutationMaskWeight p (mask.erase j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hjmask : j ∈ mask :=
        ((mem_classicalLinearCaseC2AAcceptedWithFlipAt w x i j mask).mp hmask).2
      exact mutationMaskWeight_erase_balance p mask j hjmask
    _ = ∑ z ∈ (classicalLinearCaseC2AAcceptedWithFlipAt w x i j).image
          (fun mask : MutationMask n => mask.erase j),
        p * mutationMaskWeight p z := by
      symm
      exact Finset.sum_image herase_inj
    _ ≤ ∑ z ∈ classicalLinearCaseC2AAcceptedWithoutFlipAt w x i j,
        p * mutationMaskWeight p z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      intro z hz hnotImage
      exact mul_nonneg hp0 (mutationMaskWeight_nonneg hp0 hp1 z)

/-- Marginal flip mass bound inside accepted `A_i`. -/
theorem rankLinearCaseC2AFlipAtMass_le_p_mul_acceptedMass {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i j : Fin n) (hxj : x j = true) :
    rankLinearCaseC2AFlipAtMass p w x i j ≤
      p * rankLinearCaseC2AAcceptedMass p w x i := by
  have hpair := one_sub_p_mul_rankLinearCaseC2AFlipAtMass_le
    hp0 hp1 w hw x i j hxj
  have hpart := rankLinearCaseC2AAcceptedMass_eq_flipAt_add_withoutFlipAt p w x i j
  calc
    rankLinearCaseC2AFlipAtMass p w x i j =
        (1 - p) * rankLinearCaseC2AFlipAtMass p w x i j +
          p * rankLinearCaseC2AFlipAtMass p w x i j := by ring
    _ ≤ p * rankLinearCaseC2AWithoutFlipAtMass p w x i j +
          p * rankLinearCaseC2AFlipAtMass p w x i j := by
      exact add_le_add_left hpair _
    _ = p * (rankLinearCaseC2AFlipAtMass p w x i j +
          rankLinearCaseC2AWithoutFlipAtMass p w x i j) := by ring
    _ = p * rankLinearCaseC2AAcceptedMass p w x i := by rw [← hpart]

/-- Every currently-zero coordinate contributes at least the singleton mass to `A_i`. -/
theorem linearSingletonRate_le_rankLinearCaseC2AAcceptedMass {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearSingletonRate n p ≤ rankLinearCaseC2AAcceptedMass p w x i := by
  have hmem := singleton_mem_classicalLinearCaseC2AAcceptedMasks w hw x i hi
  have hsingle :
      mutationMaskWeight p ({i} : MutationMask n) ≤
        ∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i, mutationMaskWeight p mask :=
    Finset.single_le_sum (fun mask hmask => mutationMaskWeight_nonneg hp0 hp1 mask) hmem
  simpa [rankLinearCaseC2AAcceptedMass, linearSingletonRate,
    mutationMaskWeight_singleton] using hsingle


/-- Total accepted rank-drift contribution of the `A_i` subcase. -/
noncomputable def rankLinearCaseC2AContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- Expected worsening rank mass inside accepted `A_i` masks. -/
noncomputable def rankLinearCaseC2ABadMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (∑ j ∈ oneToZeroFlips x mask, rankPotentialWeight n j)

/-- The currently-correct coordinates less important than `i`, i.e. the only
possible worsening coordinates in `A_i`. -/
def classicalLinearCaseC2ATailIndices {n : ℕ}
    (x : BitString n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = true ∧ i.val < j.val)

@[simp] theorem mem_classicalLinearCaseC2ATailIndices {n : ℕ}
    (x : BitString n) (i j : Fin n) :
    j ∈ classicalLinearCaseC2ATailIndices x i ↔
      x j = true ∧ i.val < j.val := by
  simp [classicalLinearCaseC2ATailIndices]

/-- Deterministic total rank weight of the possible worsening coordinates in `A_i`. -/
noncomputable def rankLinearCaseC2ATailRankWeight {n : ℕ}
    (x : BitString n) (i : Fin n) : ℝ :=
  ∑ j ∈ classicalLinearCaseC2ATailIndices x i, rankPotentialWeight n j

/-- Accepted `A_i` mass is nonnegative for a genuine mutation probability. -/
theorem rankLinearCaseC2AAcceptedMass_nonneg {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    0 ≤ rankLinearCaseC2AAcceptedMass p w x i := by
  unfold rankLinearCaseC2AAcceptedMass
  apply Finset.sum_nonneg
  intro mask hmask
  exact mutationMaskWeight_nonneg hp0 hp1 mask

/-- In `A_i`, a currently-one coordinate that is not strictly less important than `i`
has zero accepted flip mass. -/
theorem rankLinearCaseC2AFlipAtMass_eq_zero_of_not_lt {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n)
    (hxj : x j = true) (hji : ¬ i.val < j.val) :
    rankLinearCaseC2AFlipAtMass p w x i j = 0 := by
  unfold rankLinearCaseC2AFlipAtMass
  apply Finset.sum_eq_zero
  intro mask hmask
  have hdata :=
    (mem_classicalLinearCaseC2AAcceptedWithFlipAt w x i j mask).mp hmask
  have hA : IsClassicalLinearCaseC2A x mask i :=
    ((mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hdata.1).1
  have hjbad : j ∈ oneToZeroFlips x mask :=
    (mem_oneToZeroFlips x mask j).2 ⟨hdata.2, hxj⟩
  have hlt := index_lt_of_mem_oneToZero_of_caseC2A
    x mask i j hA hjbad
  exact (hji hlt).elim

/-- The `A_i` worsening rank mass is a coordinate sum of accepted flip masses. -/
theorem rankLinearCaseC2ABadMass_eq_sum_coordinate_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    rankLinearCaseC2ABadMass p w x i =
      ∑ j : Fin n,
        if x j = true then
          rankPotentialWeight n j * rankLinearCaseC2AFlipAtMass p w x i j
        else 0 := by
  classical
  unfold rankLinearCaseC2ABadMass
  simp_rw [oneToZeroFlips, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hxj : x j = true
  · rw [if_pos hxj]
    unfold rankLinearCaseC2AFlipAtMass classicalLinearCaseC2AAcceptedWithFlipAt
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro mask hmask
    by_cases hjm : j ∈ mask <;> simp [hxj, hjm, mul_comm]
  · rw [if_neg hxj]
    apply Finset.sum_eq_zero
    intro mask hmask
    simp [hxj]

/-- The same worsening mass restricted to the actual `A_i` tail `j>i`. -/
theorem rankLinearCaseC2ABadMass_eq_sum_tail_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    rankLinearCaseC2ABadMass p w x i =
      ∑ j ∈ classicalLinearCaseC2ATailIndices x i,
        rankPotentialWeight n j * rankLinearCaseC2AFlipAtMass p w x i j := by
  rw [rankLinearCaseC2ABadMass_eq_sum_coordinate_flipMass]
  unfold classicalLinearCaseC2ATailIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hxj : x j = true
  · by_cases hij : i.val < j.val
    · simp [hxj, hij]
    · have hzero := rankLinearCaseC2AFlipAtMass_eq_zero_of_not_lt
        p w x i j hxj hij
      simp [hxj, hij, hzero]
  · simp [hxj]

/-- Erase pairing bounds the complete `A_i` worsening rank mass by its deterministic
tail weight times `p` times accepted `A_i` mass. -/
theorem rankLinearCaseC2ABadMass_le_tailWeight_mul_p_mul_mass {n : ℕ} {p : ℝ}
    (hn : 0 < n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) :
    rankLinearCaseC2ABadMass p w x i ≤
      rankLinearCaseC2ATailRankWeight x i *
        (p * rankLinearCaseC2AAcceptedMass p w x i) := by
  rw [rankLinearCaseC2ABadMass_eq_sum_tail_flipMass]
  calc
    (∑ j ∈ classicalLinearCaseC2ATailIndices x i,
      rankPotentialWeight n j * rankLinearCaseC2AFlipAtMass p w x i j) ≤
        ∑ j ∈ classicalLinearCaseC2ATailIndices x i,
          rankPotentialWeight n j *
            (p * rankLinearCaseC2AAcceptedMass p w x i) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjdata := (mem_classicalLinearCaseC2ATailIndices x i j).mp hj
      have hflip := rankLinearCaseC2AFlipAtMass_le_p_mul_acceptedMass
        hp0 hp1 w hw x i j hjdata.1
      exact mul_le_mul_of_nonneg_left hflip
        (zero_le_one.trans (one_le_rankPotentialWeight hn j))
    _ = rankLinearCaseC2ATailRankWeight x i *
        (p * rankLinearCaseC2AAcceptedMass p w x i) := by
      unfold rankLinearCaseC2ATailRankWeight
      rw [Finset.sum_mul]

/-- Exact accepted-`A_i` contribution: good rank mass minus worsening rank mass. -/
theorem rankLinearCaseC2AContribution_eq_goodMass_sub_badMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    rankLinearCaseC2AContribution p w x i =
      rankPotentialWeight n i * rankLinearCaseC2AAcceptedMass p w x i -
        rankLinearCaseC2ABadMass p w x i := by
  unfold rankLinearCaseC2AContribution rankLinearCaseC2AAcceptedMass
    rankLinearCaseC2ABadMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  have hdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hmask
  rw [rankLinearPotential_selected_drop_eq_flip_sums_of_accepts
    w x mask hdata.2, hdata.1.1]
  simp only [Finset.sum_singleton]
  ring

/-- General finite-sum lower bound for accepted `A_i`.  The only remaining input is a
finite arithmetic bound on the deterministic tail rank weight. -/
theorem rankLinearCaseC2AContribution_ge_good_sub_tail {n : ℕ} {p : ℝ}
    (hn : 0 < n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) :
    rankPotentialWeight n i * rankLinearCaseC2AAcceptedMass p w x i -
        rankLinearCaseC2ATailRankWeight x i *
          (p * rankLinearCaseC2AAcceptedMass p w x i) ≤
      rankLinearCaseC2AContribution p w x i := by
  rw [rankLinearCaseC2AContribution_eq_goodMass_sub_badMass]
  have hbad := rankLinearCaseC2ABadMass_le_tailWeight_mul_p_mul_mass
    hn hp0 hp1 w hw x i
  linarith

/-- Eligible equal-weight swap partners for the accepted `B_i` subcase. -/
noncomputable def classicalLinearCaseC2BPartners {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j =>
    j.val < i.val ∧ x j = true ∧ w j = w i)

@[simp] theorem mem_classicalLinearCaseC2BPartners {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) :
    j ∈ classicalLinearCaseC2BPartners w x i ↔
      j.val < i.val ∧ x j = true ∧ w j = w i := by
  classical
  simp [classicalLinearCaseC2BPartners]

/-- A pair flipping a zero coordinate `i` and a distinct currently-one coordinate `j`
has exactly `{i}` as its improving flip set. -/
theorem zeroToOneFlips_pair_of_false_true {n : ℕ}
    (x : BitString n) (i j : Fin n)
    (hi : x i = false) (hj : x j = true) (hij : i ≠ j) :
    zeroToOneFlips x ({i, j} : MutationMask n) = {i} := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [zeroToOneFlips, hi, hij]
  · by_cases hkj : k = j
    · subst k
      have hji : j ≠ i := Ne.symm hij
      simp [zeroToOneFlips, hj, hji]
    · simp [zeroToOneFlips, hki, hkj]

/-- The same pair has exactly `{j}` as its worsening flip set. -/
theorem oneToZeroFlips_pair_of_false_true {n : ℕ}
    (x : BitString n) (i j : Fin n)
    (hi : x i = false) (hj : x j = true) (hij : i ≠ j) :
    oneToZeroFlips x ({i, j} : MutationMask n) = {j} := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [oneToZeroFlips, hi, hij]
  · by_cases hkj : k = j
    · subst k
      have hji : j ≠ i := Ne.symm hij
      simp [oneToZeroFlips, hj, hji]
    · simp [oneToZeroFlips, hki, hkj]

/-- Every eligible equal-weight partner gives an accepted `B_i` pair. -/
theorem pair_mem_classicalLinearCaseC2BAcceptedMasks_of_partner {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n)
    (hi : x i = false) (hj : j ∈ classicalLinearCaseC2BPartners w x i) :
    ({i, j} : MutationMask n) ∈ classicalLinearCaseC2BAcceptedMasks w x i := by
  have hjdata := (mem_classicalLinearCaseC2BPartners w x i j).mp hj
  rcases hjdata with ⟨hji, hxj, hwji⟩
  have hij : i ≠ j := by
    intro h
    subst j
    omega
  have hzero := zeroToOneFlips_pair_of_false_true x i j hi hxj hij
  have hone := oneToZeroFlips_pair_of_false_true x i j hi hxj hij
  have hB : IsClassicalLinearCaseC2B x ({i, j} : MutationMask n) i := by
    refine ⟨hzero, ?_⟩
    refine ⟨j, ?_, hji⟩
    rw [hone]
    simp
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i, j} : MutationMask n)) := by
    apply (accepts_linearFitness_iff_flip_sums w x ({i, j} : MutationMask n)).2
    rw [hzero, hone]
    simp [hwji]
  exact (mem_classicalLinearCaseC2BAcceptedMasks w x i ({i, j} : MutationMask n)).2
    ⟨hB, hacc⟩

/-- For a currently-zero `i`, accepted `B_i` masks are exactly the eligible equal-weight
pairs `{i,j}`. -/
theorem classicalLinearCaseC2BAcceptedMasks_eq_image_partners {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    classicalLinearCaseC2BAcceptedMasks w x i =
      (classicalLinearCaseC2BPartners w x i).image
        (fun j => ({i, j} : MutationMask n)) := by
  classical
  ext mask
  constructor
  · intro hmask
    have hdata := (mem_classicalLinearCaseC2BAcceptedMasks w x i mask).mp hmask
    rcases accepted_caseC2B_eq_equalWeight_pair
        w hw hmono x mask i hdata.1 hdata.2 with
      ⟨j, hjbad, hji, hwji, hone, hpair⟩
    have hxj : x j = true := ((mem_oneToZeroFlips x mask j).mp hjbad).2
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, hpair.symm⟩
    exact (mem_classicalLinearCaseC2BPartners w x i j).2 ⟨hji, hxj, hwji⟩
  · intro hmask
    rcases Finset.mem_image.mp hmask with ⟨j, hj, rfl⟩
    exact pair_mem_classicalLinearCaseC2BAcceptedMasks_of_partner w x i j hi hj

/-- Exact rank-potential drop of an eligible accepted `B_i` pair. -/
theorem rankLinearPotential_selected_drop_pair_of_partner {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n)
    (hi : x i = false) (hj : j ∈ classicalLinearCaseC2BPartners w x i) :
    rankLinearPotential x -
        rankLinearPotential
          (selectedAfterMask (linearFitness w) x ({i, j} : MutationMask n)) =
      ((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ) := by
  have hjdata := (mem_classicalLinearCaseC2BPartners w x i j).mp hj
  rcases hjdata with ⟨hji, hxj, hwji⟩
  have hij : i ≠ j := by
    intro h
    subst j
    omega
  have hzero := zeroToOneFlips_pair_of_false_true x i j hi hxj hij
  have hone := oneToZeroFlips_pair_of_false_true x i j hi hxj hij
  have hmem := pair_mem_classicalLinearCaseC2BAcceptedMasks_of_partner
    w x i j hi hj
  have hmemData := (mem_classicalLinearCaseC2BAcceptedMasks
    w x i ({i, j} : MutationMask n)).mp hmem
  have hacc := hmemData.2
  rw [rankLinearPotential_selected_drop_eq_flip_sums_of_accepts
    w x ({i, j} : MutationMask n) hacc, hzero, hone]
  simp only [Finset.sum_singleton]
  exact rankPotentialWeight_sub_eq_index_gap i j

/-- Total accepted rank-drift contribution of the `B_i` subcase. -/
noncomputable def rankLinearCaseC2BContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2BAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- The accepted `B_i` contribution is exactly a finite sum over its eligible
same-weight swap partners. -/
theorem rankLinearCaseC2BContribution_eq_partner_sum {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    rankLinearCaseC2BContribution p w x i =
      ∑ j ∈ classicalLinearCaseC2BPartners w x i,
        (p ^ 2 * (1 - p) ^ (n - 2)) *
          (((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ)) := by
  classical
  unfold rankLinearCaseC2BContribution
  rw [classicalLinearCaseC2BAcceptedMasks_eq_image_partners w hw hmono x i hi]
  have hinj :
      Set.InjOn (fun j : Fin n => ({i, j} : MutationMask n))
        ↑(classicalLinearCaseC2BPartners w x i) := by
    intro a ha b hb hab
    have hada := (mem_classicalLinearCaseC2BPartners w x i a).mp ha
    have hai : a ≠ i := by
      intro h
      subst a
      omega
    have hab' : ({i, a} : MutationMask n) = ({i, b} : MutationMask n) := by
      simpa using hab
    have hamem : a ∈ ({i, b} : MutationMask n) := by
      rw [← hab']
      simp
    have hai_or_ab : a = i ∨ a = b := by
      simpa using hamem
    exact hai_or_ab.resolve_left hai
  calc
    (∑ mask ∈ (classicalLinearCaseC2BPartners w x i).image
        (fun j => ({i, j} : MutationMask n)),
      mutationMaskWeight p mask *
        (rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) =
        ∑ j ∈ classicalLinearCaseC2BPartners w x i,
          mutationMaskWeight p ({i, j} : MutationMask n) *
            (rankLinearPotential x -
              rankLinearPotential
                (selectedAfterMask (linearFitness w) x ({i, j} : MutationMask n))) := by
      rw [Finset.sum_image]
      exact hinj
    _ = ∑ j ∈ classicalLinearCaseC2BPartners w x i,
        (p ^ 2 * (1 - p) ^ (n - 2)) *
          (((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjdata := (mem_classicalLinearCaseC2BPartners w x i j).mp hj
      have hij : i ≠ j := by
        intro h
        subst j
        omega
      rw [mutationMaskWeight_pair p i j hij,
        rankLinearPotential_selected_drop_pair_of_partner w x i j hi hj]


/-! ### Stage 10: deterministic triangular bound for the `B_i` branch -/

/-- Canonical embedding of the indices strictly below `i` back into `Fin n`. -/
def classicalLinearCaseC2BLowerEmbedding {n : ℕ}
    (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- All coordinates strictly more important than `i`, independently of the current state
or of coefficient equalities.  This is the pessimistic superset used for the triangular
`B_i` estimate. -/
noncomputable def classicalLinearCaseC2BLowerIndices {n : ℕ}
    (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (classicalLinearCaseC2BLowerEmbedding i)

@[simp] theorem mem_classicalLinearCaseC2BLowerIndices {n : ℕ}
    (i j : Fin n) :
    j ∈ classicalLinearCaseC2BLowerIndices i ↔ j.val < i.val := by
  classical
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨k, _hk, hki⟩
    rw [← hki]
    exact k.isLt
  · intro hji
    let k : Fin i.val := ⟨j.val, hji⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ k, ?_⟩
    apply Fin.ext
    rfl

/-- Every eligible equal-weight `B_i` swap partner is among the indices below `i`. -/
theorem classicalLinearCaseC2BPartners_subset_lowerIndices {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    classicalLinearCaseC2BPartners w x i ⊆
      classicalLinearCaseC2BLowerIndices i := by
  intro j hj
  apply (mem_classicalLinearCaseC2BLowerIndices i j).2
  exact ((mem_classicalLinearCaseC2BPartners w x i j).mp hj).1

/-- The reversed-rank index gap is nonpositive for a more important swap partner. -/
theorem rankIndexGap_nonpos_of_lt {n : ℕ}
    (i j : Fin n) (hji : j.val < i.val) :
    (((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ)) ≤ 0 := by
  have hcast : (j.val : ℝ) ≤ (i.val : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hji)
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcast) (Nat.cast_nonneg n)

/-- Sum of rank-index gaps over the actual equal-weight `B_i` partners. -/
noncomputable def rankLinearCaseC2BPartnerGapSum {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ j ∈ classicalLinearCaseC2BPartners w x i,
    (((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ))

/-- Pessimistic sum of rank-index gaps over every coordinate strictly below `i`. -/
noncomputable def rankLinearCaseC2BLowerGapSum {n : ℕ}
    (i : Fin n) : ℝ :=
  ∑ j ∈ classicalLinearCaseC2BLowerIndices i,
    (((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ))

/-- Because all lower-index gaps are nonpositive, adding ineligible lower coordinates can
only decrease the sum. -/
theorem rankLinearCaseC2BLowerGapSum_le_partnerGapSum {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    rankLinearCaseC2BLowerGapSum i ≤
      rankLinearCaseC2BPartnerGapSum w x i := by
  classical
  have hsubset := classicalLinearCaseC2BPartners_subset_lowerIndices w x i
  have hneg :
      (∑ j ∈ classicalLinearCaseC2BPartners w x i,
          -(((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ))) ≤
        ∑ j ∈ classicalLinearCaseC2BLowerIndices i,
          -(((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hjLower _hjNotPartner
    exact neg_nonneg.mpr <|
      rankIndexGap_nonpos_of_lt i j
        ((mem_classicalLinearCaseC2BLowerIndices i j).mp hjLower)
  unfold rankLinearCaseC2BLowerGapSum rankLinearCaseC2BPartnerGapSum
  simp only [Finset.sum_neg_distrib] at hneg
  linarith

/-- Real arithmetic-series identity used by the triangular `B_i` estimate. -/
theorem sum_range_rankIndexGap_eq_triangular (n m : ℕ) :
    (∑ j ∈ Finset.range m,
        (((j : ℝ) - (m : ℝ)) / (n : ℝ))) =
      -(((m : ℝ) * ((m : ℝ) + 1) / 2) / (n : ℝ)) := by
  have hsum :
      (∑ j ∈ Finset.range m, (j : ℝ)) =
        (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have hconst :
      (∑ _j ∈ Finset.range m, (m : ℝ)) = (m : ℝ) * (m : ℝ) := by
    rw [Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum, hconst]
  ring

/-- The pessimistic lower-index gap sum is exactly the negative triangular number divided
by `n`. -/
theorem rankLinearCaseC2BLowerGapSum_eq_triangular {n : ℕ}
    (i : Fin n) :
    rankLinearCaseC2BLowerGapSum i =
      -(((i.val : ℝ) * ((i.val : ℝ) + 1) / 2) / (n : ℝ)) := by
  classical
  have hinj :
      Set.InjOn (classicalLinearCaseC2BLowerEmbedding i)
        (↑(Finset.univ : Finset (Fin i.val))) := by
    intro a _ha b _hb hab
    apply Fin.ext
    simpa [classicalLinearCaseC2BLowerEmbedding] using
      congrArg (fun z : Fin n => z.val) hab
  calc
    rankLinearCaseC2BLowerGapSum i =
        ∑ j ∈ (Finset.univ : Finset (Fin i.val)),
          ((((classicalLinearCaseC2BLowerEmbedding i j).val : ℝ) -
              (i.val : ℝ)) / (n : ℝ)) := by
      unfold rankLinearCaseC2BLowerGapSum classicalLinearCaseC2BLowerIndices
      exact Finset.sum_image hinj
    _ = ∑ j : Fin i.val,
          (((j.val : ℝ) - (i.val : ℝ)) / (n : ℝ)) := by
      rfl
    _ = ∑ j ∈ Finset.range i.val,
          (((j : ℝ) - (i.val : ℝ)) / (n : ℝ)) := by
      symm
      simpa using
        (Finset.sum_range
          (n := i.val)
          (fun j : ℕ =>
            (((j : ℝ) - (i.val : ℝ)) / (n : ℝ))))
    _ = -(((i.val : ℝ) * ((i.val : ℝ) + 1) / 2) / (n : ℝ)) :=
      sum_range_rankIndexGap_eq_triangular n i.val

/-- Stage-9's exact partner formula factors into the common two-bit mutation weight times
the partner gap sum. -/
theorem rankLinearCaseC2BContribution_eq_pairWeight_mul_partnerGapSum {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    rankLinearCaseC2BContribution p w x i =
      (p ^ 2 * (1 - p) ^ (n - 2)) *
        rankLinearCaseC2BPartnerGapSum w x i := by
  rw [rankLinearCaseC2BContribution_eq_partner_sum p w hw hmono x i hi]
  unfold rankLinearCaseC2BPartnerGapSum
  rw [Finset.mul_sum]

/-- General triangular lower bound for the complete `B_i` contribution.  No objective
reasoning remains: the only assumptions on `p` are those needed to make the common
two-bit mutation weight nonnegative. -/
theorem rankLinearCaseC2BContribution_ge_triangular {n : ℕ} {p : ℝ}
    (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    (p ^ 2 * (1 - p) ^ (n - 2)) *
        (-(((i.val : ℝ) * ((i.val : ℝ) + 1) / 2) / (n : ℝ))) ≤
      rankLinearCaseC2BContribution p w x i := by
  rw [rankLinearCaseC2BContribution_eq_pairWeight_mul_partnerGapSum
    p w hw hmono x i hi]
  have hgap := rankLinearCaseC2BLowerGapSum_le_partnerGapSum w x i
  rw [rankLinearCaseC2BLowerGapSum_eq_triangular] at hgap
  have hpairNonneg :
      0 ≤ p ^ 2 * (1 - p) ^ (n - 2) := by
    exact mul_nonneg (sq_nonneg p) (pow_nonneg (sub_nonneg.mpr hp1) _)
  exact mul_le_mul_of_nonneg_left hgap hpairNonneg

/-- The standard singleton rate used in the linear-function proof is at least `1/(e n)`.
This is the direct-order form of the reciprocal OneMax estimate already proved in
`OneMax.lean`. -/
theorem standard_linearSingletonRate_ge_inv_en {n : ℕ} (hn : 2 ≤ n) :
    1 / (Real.exp 1 * (n : ℝ)) ≤
      linearSingletonRate n (standardMutationRate n) := by
  have hnpos : 0 < n := by omega
  have hp0 : 0 < standardMutationRate n :=
    standardMutationRate_pos hnpos
  have hp1 : standardMutationRate n < 1 :=
    standardMutationRate_lt_one hn
  have hqpos :
      0 < linearSingletonRate n (standardMutationRate n) :=
    linearSingletonRate_pos hp0 hp1
  have hrecip :
      (linearSingletonRate n (standardMutationRate n))⁻¹ ≤
        Real.exp 1 * (n : ℝ) := by
    simpa [linearSingletonRate, oneMaxImprovementRate] using
      (standardImprovementRate_inv_le_en hn)
  have hmul := mul_le_mul_of_nonneg_right hrecip hqpos.le
  have hone :
      1 ≤ (Real.exp 1 * (n : ℝ)) *
        linearSingletonRate n (standardMutationRate n) := by
    simpa [hqpos.ne'] using hmul
  have henpos : 0 < Real.exp 1 * (n : ℝ) := by
    exact mul_pos (Real.exp_pos 1) (by exact_mod_cast hnpos)
  apply (div_le_iff₀ henpos).2
  simpa [mul_comm] using hone


/-! ### Stage 11: deterministic `A_i` tail bound and local `A_i+B_i` estimate -/

/-- Reverse enumeration of all coordinates strictly less important than `i`.
The domain has exactly `n - (i+1)` elements; `k = 0` maps to the last coordinate. -/
def classicalLinearCaseC2AFullTailReverseEmbedding {n : ℕ}
    (i : Fin n) (k : Fin (n - (i.val + 1))) : Fin n :=
  ⟨n - 1 - k.val, by omega⟩

/-- The full suffix strictly below `i` in objective importance, independently of the
current bit values.  It is a deterministic superset of the actual `A_i` worsening tail. -/
noncomputable def classicalLinearCaseC2AFullTailIndices {n : ℕ}
    (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.image (classicalLinearCaseC2AFullTailReverseEmbedding i)

@[simp] theorem mem_classicalLinearCaseC2AFullTailIndices {n : ℕ}
    (i j : Fin n) :
    j ∈ classicalLinearCaseC2AFullTailIndices i ↔ i.val < j.val := by
  classical
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨k, _hk, hkj⟩
    rw [← hkj]
    change i.val < n - 1 - k.val
    omega
  · intro hij
    let k : Fin (n - (i.val + 1)) := ⟨n - 1 - j.val, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ k, ?_⟩
    apply Fin.ext
    dsimp [classicalLinearCaseC2AFullTailReverseEmbedding, k]
    omega

/-- The state-dependent `A_i` tail is contained in the deterministic full suffix. -/
theorem classicalLinearCaseC2ATailIndices_subset_fullTailIndices {n : ℕ}
    (x : BitString n) (i : Fin n) :
    classicalLinearCaseC2ATailIndices x i ⊆
      classicalLinearCaseC2AFullTailIndices i := by
  intro j hj
  exact (mem_classicalLinearCaseC2AFullTailIndices i j).2
    ((mem_classicalLinearCaseC2ATailIndices x i j).mp hj).2

/-- Rank coefficients simplify to `1 + k/n` under the reverse suffix enumeration. -/
theorem rankPotentialWeight_fullTailReverseEmbedding {n : ℕ}
    (i : Fin n) (k : Fin (n - (i.val + 1))) :
    rankPotentialWeight n (classicalLinearCaseC2AFullTailReverseEmbedding i k) =
      1 + (k.val : ℝ) / (n : ℝ) := by
  have hiLt : i.val < n := i.isLt
  have hkLt : k.val < n - (i.val + 1) := k.isLt
  have hnpos : 0 < n := Nat.zero_lt_of_lt hiLt
  have hkN : k.val < n :=
    lt_of_lt_of_le hkLt (Nat.sub_le n (i.val + 1))
  have hnatPlain : (n - 1 - k.val) + 1 + k.val = n := by
    omega
  have hnat :
      (classicalLinearCaseC2AFullTailReverseEmbedding i k).val + 1 + k.val = n := by
    simpa [classicalLinearCaseC2AFullTailReverseEmbedding] using hnatPlain
  have hreal :
      (((classicalLinearCaseC2AFullTailReverseEmbedding i k).val + 1 : ℕ) : ℝ) +
          (k.val : ℝ) = (n : ℝ) := by
    exact_mod_cast hnat
  have hnne : (n : ℝ) ≠ 0 := by positivity
  unfold rankPotentialWeight
  field_simp [hnne]
  linarith

/-- Real sum of the first `m` natural numbers, in the normalization useful below. -/
theorem sum_range_natCast_eq_triangular (m : ℕ) :
    (∑ k ∈ Finset.range m, (k : ℝ)) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Total rank weight of the deterministic suffix below `i`. -/
noncomputable def rankLinearCaseC2AFullTailRankWeight {n : ℕ}
    (i : Fin n) : ℝ :=
  ∑ j ∈ classicalLinearCaseC2AFullTailIndices i, rankPotentialWeight n j

/-- Exact arithmetic-series formula for the complete suffix rank weight. -/
theorem rankLinearCaseC2AFullTailRankWeight_eq {n : ℕ}
    (i : Fin n) :
    rankLinearCaseC2AFullTailRankWeight i =
      ((n - (i.val + 1) : ℕ) : ℝ) +
        (((n - (i.val + 1) : ℕ) : ℝ) *
            (((n - (i.val + 1) : ℕ) : ℝ) - 1) / 2) / (n : ℝ) := by
  classical
  let m : ℕ := n - (i.val + 1)
  have hinj :
      Set.InjOn (classicalLinearCaseC2AFullTailReverseEmbedding i)
        (↑(Finset.univ : Finset (Fin m))) := by
    intro a _ha b _hb hab
    apply Fin.ext
    have hval := congrArg (fun z : Fin n => z.val) hab
    dsimp [classicalLinearCaseC2AFullTailReverseEmbedding] at hval
    omega
  calc
    rankLinearCaseC2AFullTailRankWeight i =
        ∑ k ∈ (Finset.univ : Finset (Fin m)),
          rankPotentialWeight n
            (classicalLinearCaseC2AFullTailReverseEmbedding i k) := by
      unfold rankLinearCaseC2AFullTailRankWeight classicalLinearCaseC2AFullTailIndices
      exact Finset.sum_image hinj
    _ = ∑ k : Fin m, (1 + (k.val : ℝ) / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [rankPotentialWeight_fullTailReverseEmbedding i k]
    _ = ∑ k ∈ Finset.range m, (1 + (k : ℝ) / (n : ℝ)) := by
      symm
      simpa using
        (Finset.sum_range
          (n := m)
          (fun k : ℕ => 1 + (k : ℝ) / (n : ℝ)))
    _ = (m : ℝ) + ((m : ℝ) * ((m : ℝ) - 1) / 2) / (n : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hone : (∑ _k ∈ Finset.range m, (1 : ℝ)) = (m : ℝ) := by
        rw [Finset.sum_const, Finset.card_range]
        simp [nsmul_eq_mul]
      rw [hone, ← Finset.sum_div, sum_range_natCast_eq_triangular]
    _ = ((n - (i.val + 1) : ℕ) : ℝ) +
        (((n - (i.val + 1) : ℕ) : ℝ) *
            (((n - (i.val + 1) : ℕ) : ℝ) - 1) / 2) / (n : ℝ) := by
      rfl

/-- The complete suffix has average rank weight at most `3/2`. -/
theorem rankLinearCaseC2AFullTailRankWeight_le_three_halves {n : ℕ}
    (hn : 0 < n) (i : Fin n) :
    rankLinearCaseC2AFullTailRankWeight i ≤
      (3 / 2 : ℝ) * ((n - (i.val + 1) : ℕ) : ℝ) := by
  rw [rankLinearCaseC2AFullTailRankWeight_eq]
  let m : ℕ := n - (i.val + 1)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmleNat : m ≤ n := by
    dsimp [m]
    exact Nat.sub_le _ _
  have hmle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmleNat
  have hm0 : 0 ≤ (m : ℝ) / 2 := by positivity
  have hratio : ((m : ℝ) - 1) / (n : ℝ) ≤ 1 := by
    apply (div_le_one hnreal).2
    linarith
  have hscaled :
      (m : ℝ) / 2 * (((m : ℝ) - 1) / (n : ℝ)) ≤ (m : ℝ) / 2 := by
    simpa using (mul_le_mul_of_nonneg_left hratio hm0)
  change
    (m : ℝ) + ((m : ℝ) * ((m : ℝ) - 1) / 2) / (n : ℝ) ≤
      (3 / 2 : ℝ) * (m : ℝ)
  calc
    (m : ℝ) + ((m : ℝ) * ((m : ℝ) - 1) / 2) / (n : ℝ) =
        (m : ℝ) + (m : ℝ) / 2 * (((m : ℝ) - 1) / (n : ℝ)) := by ring
    _ ≤ (m : ℝ) + (m : ℝ) / 2 := by
      linarith only [hscaled]
    _ = (3 / 2 : ℝ) * (m : ℝ) := by ring

/-- The actual state-dependent `A_i` tail inherits the same `3/2`-average bound. -/
theorem rankLinearCaseC2ATailRankWeight_le_three_halves {n : ℕ}
    (hn : 0 < n) (x : BitString n) (i : Fin n) :
    rankLinearCaseC2ATailRankWeight x i ≤
      (3 / 2 : ℝ) * ((n - (i.val + 1) : ℕ) : ℝ) := by
  have hsubset := classicalLinearCaseC2ATailIndices_subset_fullTailIndices x i
  have htailFull :
      rankLinearCaseC2ATailRankWeight x i ≤
        rankLinearCaseC2AFullTailRankWeight i := by
    unfold rankLinearCaseC2ATailRankWeight rankLinearCaseC2AFullTailRankWeight
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hjFull _hjNotTail
    exact zero_le_one.trans (one_le_rankPotentialWeight hn j)
  exact htailFull.trans (rankLinearCaseC2AFullTailRankWeight_le_three_halves hn i)

/-- At the standard mutation rate, subtracting the worst possible `A_i` tail leaves the
coefficient used in the classical local drift estimate. -/
theorem standard_rankPotentialWeight_sub_tailRate_ge {n : ℕ}
    (hn : 2 ≤ n) (x : BitString n) (i : Fin n) :
    (1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ)) ≤
      rankPotentialWeight n i -
        rankLinearCaseC2ATailRankWeight x i * standardMutationRate n := by
  have hnpos : 0 < n := by omega
  have htail := rankLinearCaseC2ATailRankWeight_le_three_halves hnpos x i
  have hp0 : 0 ≤ standardMutationRate n :=
    (standardMutationRate_pos hnpos).le
  have hmul := mul_le_mul_of_nonneg_right htail hp0
  have hp : standardMutationRate n = (n : ℝ)⁻¹ := by
    simp [standardMutationRate, Nat.ne_of_gt hnpos]
  let m : ℕ := n - (i.val + 1)
  have hmNat : i.val + 1 + m = n := by
    dsimp [m]
    omega
  have hmReal : (i.val : ℝ) + 1 + (m : ℝ) = (n : ℝ) := by
    exact_mod_cast hmNat
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hexact :
      rankPotentialWeight n i -
          ((3 / 2 : ℝ) * (m : ℝ)) * standardMutationRate n =
        (1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ)) := by
    unfold rankPotentialWeight
    rw [hp]
    push_cast
    field_simp [hnne]
    linarith
  change
    (1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ)) ≤
      rankPotentialWeight n i -
        rankLinearCaseC2ATailRankWeight x i * standardMutationRate n
  rw [← hexact]
  have hmRewrite :
      ((n - (i.val + 1) : ℕ) : ℝ) = (m : ℝ) := by rfl
  rw [hmRewrite] at hmul
  linarith

/-- Standard-rate lower bound for the full accepted `A_i` contribution. -/
theorem rankLinearCaseC2AContribution_ge_standard_bonus {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearSingletonRate n (standardMutationRate n) *
        ((1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ))) ≤
      rankLinearCaseC2AContribution (standardMutationRate n) w x i := by
  have hnpos : 0 < n := by omega
  have hp := standardMutationRate_mem_unitInterval_linear hn
  have hbase := rankLinearCaseC2AContribution_ge_good_sub_tail
    hnpos hp.1 hp.2 w hw x i
  have hmass0 := rankLinearCaseC2AAcceptedMass_nonneg
    hp.1 hp.2 w x i
  have hmass := linearSingletonRate_le_rankLinearCaseC2AAcceptedMass
    hp.1 hp.2 w hw x i hi
  have hcoeff := standard_rankPotentialWeight_sub_tailRate_ge hn x i
  let d : ℝ := (1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ))
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hqMass :
      d * linearSingletonRate n (standardMutationRate n) ≤
        d * rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i :=
    mul_le_mul_of_nonneg_left hmass hd0
  have hcoeffMass :
      d * rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i ≤
        (rankPotentialWeight n i -
            rankLinearCaseC2ATailRankWeight x i * standardMutationRate n) *
          rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i :=
    mul_le_mul_of_nonneg_right hcoeff hmass0
  calc
    linearSingletonRate n (standardMutationRate n) *
        ((1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ))) =
        d * linearSingletonRate n (standardMutationRate n) := by
      dsimp [d]
      ring
    _ ≤ d * rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i := hqMass
    _ ≤ (rankPotentialWeight n i -
          rankLinearCaseC2ATailRankWeight x i * standardMutationRate n) *
        rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i := hcoeffMass
    _ = rankPotentialWeight n i *
          rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i -
        rankLinearCaseC2ATailRankWeight x i *
          (standardMutationRate n *
            rankLinearCaseC2AAcceptedMass (standardMutationRate n) w x i) := by ring
    _ ≤ rankLinearCaseC2AContribution (standardMutationRate n) w x i := hbase

/-- At the standard rate the common two-bit mutation weight, multiplied by `n-1`, is
exactly the singleton rate. -/
theorem standard_pairWeight_mul_pred_eq_linearSingletonRate {n : ℕ}
    (hn : 2 ≤ n) :
    ((n : ℝ) - 1) *
        ((standardMutationRate n) ^ 2 *
          (1 - standardMutationRate n) ^ (n - 2)) =
      linearSingletonRate n (standardMutationRate n) := by
  have hnpos : 0 < n := by omega
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hpred : n - 1 = (n - 2) + 1 := by omega
  have hpow :
      (1 - standardMutationRate n) ^ (n - 1) =
        (1 - standardMutationRate n) ^ (n - 2) *
          (1 - standardMutationRate n) := by
    rw [hpred, pow_succ]
  have hp : standardMutationRate n = (n : ℝ)⁻¹ := by
    simp [standardMutationRate, Nat.ne_of_gt hnpos]
  have hlinear :
      ((n : ℝ) - 1) * standardMutationRate n =
        1 - standardMutationRate n := by
    rw [hp]
    field_simp [hnne]
  unfold linearSingletonRate
  rw [hpow]
  calc
    ((n : ℝ) - 1) *
        ((standardMutationRate n) ^ 2 *
          (1 - standardMutationRate n) ^ (n - 2)) =
        standardMutationRate n *
          (1 - standardMutationRate n) ^ (n - 2) *
            (((n : ℝ) - 1) * standardMutationRate n) := by ring
    _ = standardMutationRate n *
          (1 - standardMutationRate n) ^ (n - 2) *
            (1 - standardMutationRate n) := by rw [hlinear]
    _ = standardMutationRate n *
          ((1 - standardMutationRate n) ^ (n - 2) *
            (1 - standardMutationRate n)) := by ring

/-- Standard-rate `B_i` loss is at worst the singleton rate times `(i+1)/(2n)`. -/
theorem rankLinearCaseC2BContribution_ge_standard_penalty {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    -(linearSingletonRate n (standardMutationRate n) *
        (((i.val : ℝ) + 1) / (2 * (n : ℝ)))) ≤
      rankLinearCaseC2BContribution (standardMutationRate n) w x i := by
  have hp1 : standardMutationRate n ≤ 1 :=
    (standardMutationRate_mem_unitInterval_linear hn).2
  have htri := rankLinearCaseC2BContribution_ge_triangular
    hp1 w hw hmono x i hi
  let r : ℝ :=
    (standardMutationRate n) ^ 2 *
      (1 - standardMutationRate n) ^ (n - 2)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (sq_nonneg (standardMutationRate n))
      (pow_nonneg (sub_nonneg.mpr hp1) _)
  have hrel :
      ((n : ℝ) - 1) * r =
        linearSingletonRate n (standardMutationRate n) := by
    dsimp [r]
    exact standard_pairWeight_mul_pred_eq_linearSingletonRate hn
  have hiLeNat : i.val + 1 ≤ n := by omega
  have hiLeCast : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hiLeNat
  have hiLe : (i.val : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hri :
      r * (i.val : ℝ) ≤ linearSingletonRate n (standardMutationRate n) := by
    calc
      r * (i.val : ℝ) ≤ r * ((n : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hiLe hr0
      _ = linearSingletonRate n (standardMutationRate n) := by
        simpa [mul_comm] using hrel
  have hnpos : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hfactor0 : 0 ≤ ((i.val : ℝ) + 1) / (2 * (n : ℝ)) := by
    exact div_nonneg (by positivity) (mul_nonneg (by norm_num) hnreal.le)
  have hscaled := mul_le_mul_of_nonneg_right hri hfactor0
  calc
    -(linearSingletonRate n (standardMutationRate n) *
        (((i.val : ℝ) + 1) / (2 * (n : ℝ)))) ≤
        -((r * (i.val : ℝ)) *
          (((i.val : ℝ) + 1) / (2 * (n : ℝ)))) := by
      exact neg_le_neg hscaled
    _ = r *
        (-(((i.val : ℝ) * ((i.val : ℝ) + 1) / 2) / (n : ℝ))) := by
      ring
    _ ≤ rankLinearCaseC2BContribution (standardMutationRate n) w x i := by
      simpa [r] using htri

/-- The complete localized C2 contribution at a zero coordinate is at least one half of
the singleton rate.  This is the local form needed for the global C2 summation. -/
theorem half_linearSingletonRate_le_rankLinearCaseC2A_add_B_standard {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearSingletonRate n (standardMutationRate n) / 2 ≤
      rankLinearCaseC2AContribution (standardMutationRate n) w x i +
        rankLinearCaseC2BContribution (standardMutationRate n) w x i := by
  have hA := rankLinearCaseC2AContribution_ge_standard_bonus
    hn w hw x i hi
  have hB := rankLinearCaseC2BContribution_ge_standard_penalty
    hn w hw hmono x i hi
  calc
    linearSingletonRate n (standardMutationRate n) / 2 =
        linearSingletonRate n (standardMutationRate n) *
            ((1 / 2 : ℝ) + ((i.val : ℝ) + 1) / (2 * (n : ℝ))) +
          (-(linearSingletonRate n (standardMutationRate n) *
            (((i.val : ℝ) + 1) / (2 * (n : ℝ))))) := by ring
    _ ≤ rankLinearCaseC2AContribution (standardMutationRate n) w x i +
        rankLinearCaseC2BContribution (standardMutationRate n) w x i :=
      add_le_add hA hB


/-! ### Stage 12: global C2 partition and rank-potential lower bound -/

/-- Total accepted rank-drift contribution of C2 masks, without choosing their unique
improving coordinate in the definition. -/
noncomputable def rankLinearCaseC2Contribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AcceptedMasks w x,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- Total accepted C2 contribution localized at its unique improving coordinate `i`. -/
noncomputable def rankLinearCaseC2AtContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- The accepted `A_i` and `B_i` mask sets are disjoint. -/
theorem classicalLinearCaseC2AAcceptedMasks_disjoint_B {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    Disjoint (classicalLinearCaseC2AAcceptedMasks w x i)
      (classicalLinearCaseC2BAcceptedMasks w x i) := by
  classical
  rw [Finset.disjoint_left]
  intro mask hA hB
  have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hA
  have hBdata := (mem_classicalLinearCaseC2BAcceptedMasks w x i mask).mp hB
  rcases hBdata.1.2 with ⟨j, hj, hji⟩
  exact hAdata.1.2 j hj hji

/-- For a fixed improving coordinate, the full accepted C2 contribution is exactly the
sum of its `A_i` and `B_i` pieces. -/
theorem rankLinearCaseC2AtContribution_eq_A_add_B {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    rankLinearCaseC2AtContribution p w x i =
      rankLinearCaseC2AContribution p w x i +
        rankLinearCaseC2BContribution p w x i := by
  classical
  unfold rankLinearCaseC2AtContribution rankLinearCaseC2AContribution
    rankLinearCaseC2BContribution
  rw [classicalLinearCaseC2AtAcceptedMasks_eq_A_union_B w x i]
  exact Finset.sum_union (classicalLinearCaseC2AAcceptedMasks_disjoint_B w x i)

/-- Pointwise uniqueness identity behind the global C2 partition: a C2 mask contributes
through exactly one zero coordinate, namely its unique zero-to-one flip. -/
theorem sum_zeroPositions_caseC2At_indicator_eq_caseC2_indicator {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (a : ℝ) :
    (∑ i ∈ zeroPositions x,
      if mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i then a else 0) =
      if mask ∈ classicalLinearCaseC2AcceptedMasks w x then a else 0 := by
  classical
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · by_cases hC2 : IsClassicalLinearCaseC2 x mask
    · have hcard : (zeroToOneFlips x mask).card = 1 := by
        simpa [IsClassicalLinearCaseC2, zeroToOneFlipCount] using hC2
      have hpos : 0 < (zeroToOneFlips x mask).card := by omega
      rcases Finset.card_pos.mp hpos with ⟨i, hi⟩
      have hAt : IsClassicalLinearCaseC2At x mask i :=
        classicalLinearCaseC2At_of_caseC2_of_mem x mask i hC2 hi
      have hi0 : x i = false :=
        false_of_classicalLinearCaseC2At x mask i hAt
      have hiZero : i ∈ zeroPositions x := (mem_zeroPositions x i).2 hi0
      have hunique : ∀ j : Fin n, IsClassicalLinearCaseC2At x mask j ↔ j = i := by
        intro j
        constructor
        · intro hAtj
          have hZi : zeroToOneFlips x mask = ({i} : Finset (Fin n)) := hAt
          have hZj : zeroToOneFlips x mask = ({j} : Finset (Fin n)) := hAtj
          have hs : ({j} : Finset (Fin n)) = {i} := by
            rw [← hZj, hZi]
          exact Finset.singleton_injective hs
        · intro hji
          subst j
          exact hAt
      calc
        (∑ j ∈ zeroPositions x,
          if mask ∈ classicalLinearCaseC2AtAcceptedMasks w x j then a else 0) =
            (if mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i
              then a else 0) := by
            apply Finset.sum_eq_single_of_mem i hiZero
            intro j hj hji
            rw [if_neg]
            intro hmem
            have hAtj : IsClassicalLinearCaseC2At x mask j :=
              ((mem_classicalLinearCaseC2AtAcceptedMasks w x j mask).mp hmem).1
            exact hji ((hunique j).mp hAtj)
        _ = a := by simp [hAt, hacc]
        _ = if mask ∈ classicalLinearCaseC2AcceptedMasks w x
            then a else 0 := by simp [hC2, hacc]
    · have hnoAt : ∀ i : Fin n, ¬ IsClassicalLinearCaseC2At x mask i := by
        intro i hAt
        exact hC2 (classicalLinearCaseC2_of_caseC2At x mask i hAt)
      simp [hacc, hC2, hnoAt]
  · simp [hacc]

/-- Accepted C2 masks partition exactly by their unique improving zero coordinate. -/
theorem rankLinearCaseC2Contribution_eq_sum_zeroPositions_at {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    rankLinearCaseC2Contribution p w x =
      ∑ i ∈ zeroPositions x, rankLinearCaseC2AtContribution p w x i := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))
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

/-- Global accepted C2 contribution is the sum of the localized `A_i+B_i` terms over
currently-zero coordinates. -/
theorem rankLinearCaseC2Contribution_eq_sum_zeroPositions_A_add_B {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    rankLinearCaseC2Contribution p w x =
      ∑ i ∈ zeroPositions x,
        (rankLinearCaseC2AContribution p w x i +
          rankLinearCaseC2BContribution p w x i) := by
  rw [rankLinearCaseC2Contribution_eq_sum_zeroPositions_at]
  apply Finset.sum_congr rfl
  intro i hi
  exact rankLinearCaseC2AtContribution_eq_A_add_B p w x i

/-- At the standard rate, the complete C2 contribution is at least one half singleton
rate per currently-zero coordinate. -/
theorem half_rate_mul_zeroCount_le_rankLinearCaseC2Contribution_standard {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    (zeroCount x : ℝ) *
        (linearSingletonRate n (standardMutationRate n) / 2) ≤
      rankLinearCaseC2Contribution (standardMutationRate n) w x := by
  rw [rankLinearCaseC2Contribution_eq_sum_zeroPositions_A_add_B]
  have hsum :
      (∑ i ∈ zeroPositions x,
        linearSingletonRate n (standardMutationRate n) / 2) ≤
        ∑ i ∈ zeroPositions x,
          (rankLinearCaseC2AContribution (standardMutationRate n) w x i +
            rankLinearCaseC2BContribution (standardMutationRate n) w x i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact half_linearSingletonRate_le_rankLinearCaseC2A_add_B_standard
      hn w hw hmono x i ((mem_zeroPositions x i).mp hi)
  simpa [Finset.sum_const, nsmul_eq_mul, zeroPositions_card] using hsum

/-- Global C2 rank drift controls one quarter of the rank potential times the singleton
rate.  This is the coefficient-independent C2 estimate needed in the final C1/C2/C3
assembly. -/
theorem quarter_rate_mul_rankLinearPotential_le_rankLinearCaseC2Contribution_standard
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    (linearSingletonRate n (standardMutationRate n) / 4) * rankLinearPotential x ≤
      rankLinearCaseC2Contribution (standardMutationRate n) w x := by
  have hnpos : 0 < n := by omega
  have hq0 : 0 ≤ linearSingletonRate n (standardMutationRate n) :=
    (linearSingletonRate_pos
      (standardMutationRate_pos hnpos) (standardMutationRate_lt_one hn)).le
  have hhalfV : rankLinearPotential x / 2 ≤ (zeroCount x : ℝ) := by
    have hV := rankLinearPotential_le_two_mul_zeroCount x
    linarith
  have hscale0 : 0 ≤ linearSingletonRate n (standardMutationRate n) / 2 := by
    exact div_nonneg hq0 (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hhalfV hscale0
  have hC2 := half_rate_mul_zeroCount_le_rankLinearCaseC2Contribution_standard
    hn w hw hmono x
  calc
    (linearSingletonRate n (standardMutationRate n) / 4) * rankLinearPotential x =
        (linearSingletonRate n (standardMutationRate n) / 2) *
          (rankLinearPotential x / 2) := by ring
    _ ≤ (linearSingletonRate n (standardMutationRate n) / 2) *
          (zeroCount x : ℝ) := hscaled
    _ = (zeroCount x : ℝ) *
          (linearSingletonRate n (standardMutationRate n) / 2) := by ring
    _ ≤ rankLinearCaseC2Contribution (standardMutationRate n) w x := hC2


/-- In C3 the improving side of the rank-potential change has total weight at least two. -/
theorem two_le_rankPotentialWeight_sum_zeroToOne_of_caseC3 {n : ℕ}
    (x : BitString n) (mask : MutationMask n)
    (hC3 : IsClassicalLinearCaseC3 x mask) :
    (2 : ℝ) ≤ ∑ i ∈ zeroToOneFlips x mask, rankPotentialWeight n i := by
  have hcard : 2 ≤ (zeroToOneFlips x mask).card := by
    simpa [IsClassicalLinearCaseC3, zeroToOneFlipCount] using hC3
  have hcardle : (zeroToOneFlips x mask).card ≤ n := by
    simpa using (Finset.card_le_univ (zeroToOneFlips x mask))
  have hnpos : 0 < n := by omega
  calc
    (2 : ℝ) ≤ ((zeroToOneFlips x mask).card : ℝ) := by exact_mod_cast hcard
    _ = ∑ _i ∈ zeroToOneFlips x mask, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ zeroToOneFlips x mask, rankPotentialWeight n i := by
      apply Finset.sum_le_sum
      intro i hi
      exact one_le_rankPotentialWeight hnpos i

/-- Every accepted C3 mask has rank drop at least two minus its worsening rank mass. -/
theorem rankLinearPotential_selected_drop_ge_two_sub_bad_of_caseC3 {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hC3 : IsClassicalLinearCaseC3 x mask)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    (2 : ℝ) - (∑ i ∈ oneToZeroFlips x mask, rankPotentialWeight n i) ≤
      rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask) := by
  rw [rankLinearPotential_selected_drop_eq_flip_sums_of_accepts w x mask hacc]
  have hpos := two_le_rankPotentialWeight_sum_zeroToOne_of_caseC3 x mask hC3
  linarith

/-- Accepted masks in C3.  Rejected C3 masks contribute zero after elitist selection. -/
noncomputable def classicalLinearCaseC3AcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) : Finset (MutationMask n) := by
  classical
  exact (classicalLinearCaseC3Masks x).filter
    (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask))

@[simp] theorem mem_classicalLinearCaseC3AcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC3AcceptedMasks w x ↔
      IsClassicalLinearCaseC3 x mask ∧
        Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  simp [classicalLinearCaseC3AcceptedMasks]

/--
Erasing any worsening flip from an accepted C3 mask stays inside the accepted C3 set.
This is the structural half of the finite-mask injection used to control C3.
-/
theorem erase_oneToZero_mem_classicalLinearCaseC3AcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (j : Fin n)
    (hmask : mask ∈ classicalLinearCaseC3AcceptedMasks w x)
    (hj : j ∈ oneToZeroFlips x mask) :
    mask.erase j ∈ classicalLinearCaseC3AcceptedMasks w x := by
  have hdata := (mem_classicalLinearCaseC3AcceptedMasks w x mask).mp hmask
  have hjdata := (mem_oneToZeroFlips x mask j).mp hj
  apply (mem_classicalLinearCaseC3AcceptedMasks w x (mask.erase j)).2
  exact ⟨
    classicalLinearCaseC3_erase_of_true x mask j hjdata.2 hdata.1,
    accepts_erase_oneToZero_of_accepts w hw x mask j hjdata.1 hjdata.2 hdata.2
  ⟩

/-- Accepted C3 masks that flip a specified coordinate. -/
noncomputable def classicalLinearCaseC3AcceptedWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (j : Fin n) : Finset (MutationMask n) := by
  classical
  exact (classicalLinearCaseC3AcceptedMasks w x).filter (fun mask => j ∈ mask)

/-- Accepted C3 masks that do not flip a specified coordinate. -/
noncomputable def classicalLinearCaseC3AcceptedWithoutFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (j : Fin n) : Finset (MutationMask n) := by
  classical
  exact (classicalLinearCaseC3AcceptedMasks w x).filter (fun mask => j ∉ mask)

@[simp] theorem mem_classicalLinearCaseC3AcceptedWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (j : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC3AcceptedWithFlipAt w x j ↔
      mask ∈ classicalLinearCaseC3AcceptedMasks w x ∧ j ∈ mask := by
  classical
  simp [classicalLinearCaseC3AcceptedWithFlipAt]

@[simp] theorem mem_classicalLinearCaseC3AcceptedWithoutFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (j : Fin n) (mask : MutationMask n) :
    mask ∈ classicalLinearCaseC3AcceptedWithoutFlipAt w x j ↔
      mask ∈ classicalLinearCaseC3AcceptedMasks w x ∧ j ∉ mask := by
  classical
  simp [classicalLinearCaseC3AcceptedWithoutFlipAt]

/-- Total mutation probability mass of accepted C3 masks. -/
noncomputable def rankLinearCaseC3AcceptedMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x, mutationMaskWeight p mask

/-- Accepted C3 probability mass among masks that flip coordinate `j`. -/
noncomputable def rankLinearCaseC3FlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (j : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedWithFlipAt w x j, mutationMaskWeight p mask

/-- Accepted C3 probability mass among masks that do not flip coordinate `j`. -/
noncomputable def rankLinearCaseC3WithoutFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (j : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedWithoutFlipAt w x j, mutationMaskWeight p mask

/-- Accepted C3 mass partitions according to whether a fixed coordinate flips. -/
theorem rankLinearCaseC3AcceptedMass_eq_flipAt_add_withoutFlipAt {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (j : Fin n) :
    rankLinearCaseC3AcceptedMass p w x =
      rankLinearCaseC3FlipAtMass p w x j +
        rankLinearCaseC3WithoutFlipAtMass p w x j := by
  classical
  unfold rankLinearCaseC3AcceptedMass rankLinearCaseC3FlipAtMass
    rankLinearCaseC3WithoutFlipAtMass
    classicalLinearCaseC3AcceptedWithFlipAt classicalLinearCaseC3AcceptedWithoutFlipAt
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hj : j ∈ mask <;> simp [hj]

/--
Erasure pairing for one currently-correct coordinate.  The weighted mass of accepted
C3 masks that flip `j`, multiplied by `1-p`, is at most `p` times the mass of accepted
C3 masks that do not flip `j`.
-/
theorem one_sub_p_mul_rankLinearCaseC3FlipAtMass_le
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (j : Fin n) (hxj : x j = true) :
    (1 - p) * rankLinearCaseC3FlipAtMass p w x j ≤
      p * rankLinearCaseC3WithoutFlipAtMass p w x j := by
  classical
  unfold rankLinearCaseC3FlipAtMass rankLinearCaseC3WithoutFlipAtMass
  rw [Finset.mul_sum, Finset.mul_sum]
  have herase_inj :
      Set.InjOn (fun mask : MutationMask n => mask.erase j)
        ↑(classicalLinearCaseC3AcceptedWithFlipAt w x j) := by
    intro a ha b hb hab
    have hja : j ∈ a := ((mem_classicalLinearCaseC3AcceptedWithFlipAt w x j a).mp ha).2
    have hjb : j ∈ b := ((mem_classicalLinearCaseC3AcceptedWithFlipAt w x j b).mp hb).2
    have hab' : a.erase j = b.erase j := by
      simpa using hab
    calc
      a = insert j (a.erase j) := (Finset.insert_erase hja).symm
      _ = insert j (b.erase j) := by rw [hab']
      _ = b := Finset.insert_erase hjb
  have himage_subset :
      (classicalLinearCaseC3AcceptedWithFlipAt w x j).image
          (fun mask : MutationMask n => mask.erase j) ⊆
        classicalLinearCaseC3AcceptedWithoutFlipAt w x j := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨mask, hmask, rfl⟩
    have hmaskData := (mem_classicalLinearCaseC3AcceptedWithFlipAt w x j mask).mp hmask
    apply (mem_classicalLinearCaseC3AcceptedWithoutFlipAt w x j (mask.erase j)).2
    have hjbad : j ∈ oneToZeroFlips x mask :=
      (mem_oneToZeroFlips x mask j).2 ⟨hmaskData.2, hxj⟩
    exact ⟨erase_oneToZero_mem_classicalLinearCaseC3AcceptedMasks
      w hw x mask j hmaskData.1 hjbad, by simp⟩
  calc
    (∑ mask ∈ classicalLinearCaseC3AcceptedWithFlipAt w x j,
        (1 - p) * mutationMaskWeight p mask) =
      ∑ mask ∈ classicalLinearCaseC3AcceptedWithFlipAt w x j,
        p * mutationMaskWeight p (mask.erase j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hjmask : j ∈ mask :=
        ((mem_classicalLinearCaseC3AcceptedWithFlipAt w x j mask).mp hmask).2
      exact mutationMaskWeight_erase_balance p mask j hjmask
    _ = ∑ z ∈ (classicalLinearCaseC3AcceptedWithFlipAt w x j).image
          (fun mask : MutationMask n => mask.erase j),
        p * mutationMaskWeight p z := by
      symm
      exact Finset.sum_image herase_inj
    _ ≤ ∑ z ∈ classicalLinearCaseC3AcceptedWithoutFlipAt w x j,
        p * mutationMaskWeight p z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      intro z hz hnotImage
      exact mul_nonneg hp0 (mutationMaskWeight_nonneg hp0 hp1 z)

/-- For a currently-correct coordinate, accepted C3 conditioning cannot increase its flip mass. -/
theorem rankLinearCaseC3FlipAtMass_le_p_mul_acceptedMass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (j : Fin n) (hxj : x j = true) :
    rankLinearCaseC3FlipAtMass p w x j ≤
      p * rankLinearCaseC3AcceptedMass p w x := by
  have hpair := one_sub_p_mul_rankLinearCaseC3FlipAtMass_le
    hp0 hp1 w hw x j hxj
  have hpart := rankLinearCaseC3AcceptedMass_eq_flipAt_add_withoutFlipAt p w x j
  calc
    rankLinearCaseC3FlipAtMass p w x j =
        (1 - p) * rankLinearCaseC3FlipAtMass p w x j +
          p * rankLinearCaseC3FlipAtMass p w x j := by ring
    _ ≤ p * rankLinearCaseC3WithoutFlipAtMass p w x j +
          p * rankLinearCaseC3FlipAtMass p w x j := by
      exact add_le_add_left hpair _
    _ = p * (rankLinearCaseC3FlipAtMass p w x j +
          rankLinearCaseC3WithoutFlipAtMass p w x j) := by ring
    _ = p * rankLinearCaseC3AcceptedMass p w x := by rw [← hpart]

/-- Expected worsening rank mass carried by accepted C3 masks. -/
noncomputable def rankLinearCaseC3BadMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x,
    mutationMaskWeight p mask *
      (∑ i ∈ oneToZeroFlips x mask, rankPotentialWeight n i)

/-- Accepted C3 mass is nonnegative for a genuine mutation probability. -/
theorem rankLinearCaseC3AcceptedMass_nonneg {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : Fin n → ℝ) (x : BitString n) :
    0 ≤ rankLinearCaseC3AcceptedMass p w x := by
  unfold rankLinearCaseC3AcceptedMass
  apply Finset.sum_nonneg
  intro mask hmask
  exact mutationMaskWeight_nonneg hp0 hp1 mask

/-- The C3 worsening rank mass can be written as a sum of coordinate flip masses. -/
theorem rankLinearCaseC3BadMass_eq_sum_coordinate_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    rankLinearCaseC3BadMass p w x =
      ∑ i : Fin n,
        if x i = true then
          rankPotentialWeight n i * rankLinearCaseC3FlipAtMass p w x i
        else 0 := by
  classical
  unfold rankLinearCaseC3BadMass
  simp_rw [oneToZeroFlips, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x i = true
  · rw [if_pos hxi]
    unfold rankLinearCaseC3FlipAtMass classicalLinearCaseC3AcceptedWithFlipAt
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro mask hmask
    by_cases him : i ∈ mask <;> simp [hxi, him, mul_comm]
  · rw [if_neg hxi]
    apply Finset.sum_eq_zero
    intro mask hmask
    simp [hxi]

/-- General C3 bad-mass bound before specializing the mutation rate. -/
theorem rankLinearCaseC3BadMass_le_two_mul_n_mul_p_mul_mass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    rankLinearCaseC3BadMass p w x ≤
      2 * (n : ℝ) * p * rankLinearCaseC3AcceptedMass p w x := by
  rw [rankLinearCaseC3BadMass_eq_sum_coordinate_flipMass]
  have hmass0 : 0 ≤ rankLinearCaseC3AcceptedMass p w x :=
    rankLinearCaseC3AcceptedMass_nonneg hp0 hp1 w x
  have hpmass0 : 0 ≤ p * rankLinearCaseC3AcceptedMass p w x :=
    mul_nonneg hp0 hmass0
  calc
    (∑ i : Fin n,
      if x i = true then
        rankPotentialWeight n i * rankLinearCaseC3FlipAtMass p w x i
      else 0) ≤
        ∑ _i : Fin n, 2 * (p * rankLinearCaseC3AcceptedMass p w x) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hxi : x i = true
      · rw [if_pos hxi]
        have hflip := rankLinearCaseC3FlipAtMass_le_p_mul_acceptedMass
          hp0 hp1 w hw x i hxi
        have hflip0 : 0 ≤ rankLinearCaseC3FlipAtMass p w x i := by
          unfold rankLinearCaseC3FlipAtMass
          apply Finset.sum_nonneg
          intro mask hmask
          exact mutationMaskWeight_nonneg hp0 hp1 mask
        exact mul_le_mul (rankPotentialWeight_le_two i) hflip hflip0 (by norm_num)
      · rw [if_neg hxi]
        exact mul_nonneg (by norm_num) hpmass0
    _ = 2 * (n : ℝ) * p * rankLinearCaseC3AcceptedMass p w x := by
      simp [nsmul_eq_mul]
      ring

/-- At the standard rate, the C3 worsening mass is at most twice accepted C3 mass. -/
theorem rankLinearCaseC3BadMass_le_two_mul_acceptedMass_standard
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    rankLinearCaseC3BadMass (standardMutationRate n) w x ≤
      2 * rankLinearCaseC3AcceptedMass (standardMutationRate n) w x := by
  have hp := standardMutationRate_mem_unitInterval_linear hn
  have h := rankLinearCaseC3BadMass_le_two_mul_n_mul_p_mul_mass
    hp.1 hp.2 w hw x
  have hnpos : 0 < n := by omega
  have hnne : (n : ℝ) ≠ 0 := by positivity
  rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)] at h ⊢
  simpa [hnne, mul_assoc] using h

/-- Rank-drift contribution of accepted C3 masks. -/
noncomputable def rankLinearCaseC3AcceptedContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- Rank-drift contribution of all C3 masks, accepted or rejected. -/
noncomputable def rankLinearCaseC3Contribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3Masks x,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- Rejected C3 masks vanish, so the full C3 contribution equals the accepted part. -/
theorem rankLinearCaseC3Contribution_eq_accepted {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    rankLinearCaseC3Contribution p w x =
      rankLinearCaseC3AcceptedContribution p w x := by
  classical
  unfold rankLinearCaseC3Contribution rankLinearCaseC3AcceptedContribution
    classicalLinearCaseC3AcceptedMasks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp [hacc]
  · rw [rankLinearPotential_selected_drop_of_rejects w x mask hacc]
    simp [hacc]

/-- Deterministic C3 reduction: contribution is at least `2 * mass - badMass`. -/
theorem two_mul_rankLinearCaseC3AcceptedMass_sub_badMass_le_contribution
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) :
    2 * rankLinearCaseC3AcceptedMass p w x - rankLinearCaseC3BadMass p w x ≤
      rankLinearCaseC3AcceptedContribution p w x := by
  unfold rankLinearCaseC3AcceptedMass rankLinearCaseC3BadMass
    rankLinearCaseC3AcceptedContribution
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro mask hmask
  have hmem := (mem_classicalLinearCaseC3AcceptedMasks w x mask).mp hmask
  have hdrop := rankLinearPotential_selected_drop_ge_two_sub_bad_of_caseC3
    w x mask hmem.1 hmem.2
  have hwt : 0 ≤ mutationMaskWeight p mask := mutationMaskWeight_nonneg hp0 hp1 mask
  have hmul := mul_le_mul_of_nonneg_left hdrop hwt
  nlinarith

/-- If the expected worsening rank mass is at most twice C3 mass, C3 is nonnegative. -/
theorem rankLinearCaseC3Contribution_nonneg_of_badMass_le
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n)
    (hbad : rankLinearCaseC3BadMass p w x ≤
      2 * rankLinearCaseC3AcceptedMass p w x) :
    0 ≤ rankLinearCaseC3Contribution p w x := by
  rw [rankLinearCaseC3Contribution_eq_accepted]
  have hlower := two_mul_rankLinearCaseC3AcceptedMass_sub_badMass_le_contribution
    hp0 hp1 w x
  linarith

/-- Named standard-rate C3 bad-mass property, now discharged by the erase-map argument. -/
def HasClassicalLinearCaseC3BadMassBound {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ x : BitString n,
    rankLinearCaseC3BadMass (standardMutationRate n) w x ≤
      2 * rankLinearCaseC3AcceptedMass (standardMutationRate n) w x

/-- Positive linear weights satisfy the complete C3 bad-mass bound at the standard rate. -/
theorem hasClassicalLinearCaseC3BadMassBound_of_positive
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ) (hw : PositiveLinearWeights w) :
    HasClassicalLinearCaseC3BadMassBound w := by
  intro x
  exact rankLinearCaseC3BadMass_le_two_mul_acceptedMass_standard hn w hw x

/-- The aggregate C3 rank-drift contribution is nonnegative at the standard mutation rate. -/
theorem rankLinearCaseC3Contribution_nonneg_standard
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) :
    0 ≤ rankLinearCaseC3Contribution (standardMutationRate n) w x := by
  have hp := standardMutationRate_mem_unitInterval_linear hn
  exact rankLinearCaseC3Contribution_nonneg_of_badMass_le
    hp.1 hp.2 w x
    (rankLinearCaseC3BadMass_le_two_mul_acceptedMass_standard hn w hw x)

/-- The complete C1 contribution to rank drift is zero for positive linear weights. -/
theorem rankLinear_caseC1_contribution_eq_zero
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ classicalLinearCaseC1Masks x,
      mutationMaskWeight p mask *
        (rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) = 0 := by
  apply Finset.sum_eq_zero
  intro mask hmask
  have hC1 : IsClassicalLinearCaseC1 x mask :=
    (mem_classicalLinearCaseC1Masks x mask).mp hmask
  rw [rankLinearPotential_selected_drop_eq_zero_of_caseC1 w hw x mask hC1]
  ring

/-! ### Stage 13: full C1/C2/C3 drift assembly -/

/-- Rejected C2 masks have zero selected drop, so the accepted-C2 contribution equals
its raw sum over the complete numerical C2 class. -/
theorem rankLinearCaseC2Contribution_eq_all {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    rankLinearCaseC2Contribution p w x =
      ∑ mask ∈ classicalLinearCaseC2Masks x,
        mutationMaskWeight p mask *
          (rankLinearPotential x -
            rankLinearPotential (selectedAfterMask (linearFitness w) x mask)) := by
  classical
  unfold rankLinearCaseC2Contribution classicalLinearCaseC2AcceptedMasks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp [hacc]
  · rw [rankLinearPotential_selected_drop_of_rejects w x mask hacc]
    simp [hacc]

/-- The numerical C1 and C2 mask classes are disjoint. -/
theorem classicalLinearCaseC1Masks_disjoint_C2Masks {n : ℕ}
    (x : BitString n) :
    Disjoint (classicalLinearCaseC1Masks x) (classicalLinearCaseC2Masks x) := by
  classical
  rw [Finset.disjoint_left]
  intro mask hC1mem hC2mem
  have hC1 : IsClassicalLinearCaseC1 x mask :=
    (mem_classicalLinearCaseC1Masks x mask).mp hC1mem
  have hC2 : IsClassicalLinearCaseC2 x mask :=
    (mem_classicalLinearCaseC2Masks x mask).mp hC2mem
  unfold IsClassicalLinearCaseC1 at hC1
  unfold IsClassicalLinearCaseC2 at hC2
  omega

/-- The union of C1 and C2 is disjoint from C3. -/
theorem classicalLinearCaseC1_union_C2_disjoint_C3Masks {n : ℕ}
    (x : BitString n) :
    Disjoint (classicalLinearCaseC1Masks x ∪ classicalLinearCaseC2Masks x)
      (classicalLinearCaseC3Masks x) := by
  classical
  rw [Finset.disjoint_left]
  intro mask hC12mem hC3mem
  have hC3 : IsClassicalLinearCaseC3 x mask :=
    (mem_classicalLinearCaseC3Masks x mask).mp hC3mem
  rcases Finset.mem_union.mp hC12mem with hC1mem | hC2mem
  · have hC1 : IsClassicalLinearCaseC1 x mask :=
      (mem_classicalLinearCaseC1Masks x mask).mp hC1mem
    unfold IsClassicalLinearCaseC1 at hC1
    unfold IsClassicalLinearCaseC3 at hC3
    omega
  · have hC2 : IsClassicalLinearCaseC2 x mask :=
      (mem_classicalLinearCaseC2Masks x mask).mp hC2mem
    unfold IsClassicalLinearCaseC2 at hC2
    unfold IsClassicalLinearCaseC3 at hC3
    omega

/-- C1, C2, and C3 cover every mutation mask. -/
theorem classicalLinearCaseMasks_union_eq_univ {n : ℕ}
    (x : BitString n) :
    (classicalLinearCaseC1Masks x ∪ classicalLinearCaseC2Masks x) ∪
        classicalLinearCaseC3Masks x =
      (Finset.univ : Finset (MutationMask n)) := by
  classical
  ext mask
  constructor
  · intro _h
    exact Finset.mem_univ mask
  · intro _h
    rcases classicalLinearCase_trichotomy x mask with hC1 | hC2 | hC3
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inl ((mem_classicalLinearCaseC1Masks x mask).2 hC1))))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inr ((mem_classicalLinearCaseC2Masks x mask).2 hC2))))
    · exact Finset.mem_union.mpr
        (Or.inr ((mem_classicalLinearCaseC3Masks x mask).2 hC3))

/-- The complete mutation-mask sum is exactly the sum of its C1, C2, and C3 pieces. -/
theorem rankLinear_mask_sum_eq_case_sums {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    (∑ mask : MutationMask n,
      mutationMaskWeight p mask *
        (rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) =
      (∑ mask ∈ classicalLinearCaseC1Masks x,
        mutationMaskWeight p mask *
          (rankLinearPotential x -
            rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) +
      (∑ mask ∈ classicalLinearCaseC2Masks x,
        mutationMaskWeight p mask *
          (rankLinearPotential x -
            rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) +
      (∑ mask ∈ classicalLinearCaseC3Masks x,
        mutationMaskWeight p mask *
          (rankLinearPotential x -
            rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))
  change (∑ mask : MutationMask n, F mask) =
    (∑ mask ∈ classicalLinearCaseC1Masks x, F mask) +
      (∑ mask ∈ classicalLinearCaseC2Masks x, F mask) +
        (∑ mask ∈ classicalLinearCaseC3Masks x, F mask)
  have h12 := classicalLinearCaseC1Masks_disjoint_C2Masks x
  have h123 := classicalLinearCaseC1_union_C2_disjoint_C3Masks x
  calc
    (∑ mask : MutationMask n, F mask) =
        ∑ mask ∈
          ((classicalLinearCaseC1Masks x ∪ classicalLinearCaseC2Masks x) ∪
            classicalLinearCaseC3Masks x), F mask := by
          rw [classicalLinearCaseMasks_union_eq_univ x]
    _ = (∑ mask ∈ classicalLinearCaseC1Masks x ∪ classicalLinearCaseC2Masks x,
          F mask) +
        (∑ mask ∈ classicalLinearCaseC3Masks x, F mask) :=
          Finset.sum_union h123
    _ = ((∑ mask ∈ classicalLinearCaseC1Masks x, F mask) +
          (∑ mask ∈ classicalLinearCaseC2Masks x, F mask)) +
        (∑ mask ∈ classicalLinearCaseC3Masks x, F mask) := by
          rw [Finset.sum_union h12]

/-- For positive linear weights, full rank drift is exactly the sum of the C2 and C3
contributions: C1 is zero and rejected C2 masks vanish. -/
theorem rankLinear_drift_eq_caseC2_add_caseC3 {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (rankLinearPotential (n := n)) x =
      rankLinearCaseC2Contribution p w x +
        rankLinearCaseC3Contribution p w x := by
  rw [rankLinear_drift_eq_mask_sum]
  rw [rankLinear_mask_sum_eq_case_sums]
  rw [rankLinear_caseC1_contribution_eq_zero (p := p) w hw x]
  rw [← rankLinearCaseC2Contribution_eq_all p w x]
  simp only [zero_add, rankLinearCaseC3Contribution]

/-- At the standard mutation rate, the complete rank drift is at least one quarter of
the singleton rate times the rank potential. -/
theorem quarter_rate_mul_rankLinearPotential_le_drift_standard
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    (linearSingletonRate n (standardMutationRate n) / 4) * rankLinearPotential x ≤
      driftAt
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearPotential (n := n)) x := by
  rw [rankLinear_drift_eq_caseC2_add_caseC3
    (standardMutationRate n) w hw x]
  have hC2 :=
    quarter_rate_mul_rankLinearPotential_le_rankLinearCaseC2Contribution_standard
      hn w hw hmono x
  have hC3 := rankLinearCaseC3Contribution_nonneg_standard hn w hw x
  linarith

/-- The textbook rate `1/(4 e n)` is at most one quarter of the standard singleton
mutation rate. -/
theorem classicalLinearDriftRate_le_quarter_standardSingletonRate
    {n : ℕ} (hn : 2 ≤ n) :
    classicalLinearDriftRate n ≤
      linearSingletonRate n (standardMutationRate n) / 4 := by
  have hq := standard_linearSingletonRate_ge_inv_en hn
  have hscaled := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ (1 / 4 : ℝ) by norm_num)
  have hnpos : 0 < n := by omega
  have hnne : (n : ℝ) ≠ 0 := by positivity
  have hene : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  calc
    classicalLinearDriftRate n =
        (1 / (Real.exp 1 * (n : ℝ))) * (1 / 4 : ℝ) := by
          unfold classicalLinearDriftRate
          field_simp [hnne, hene]
    _ ≤ linearSingletonRate n (standardMutationRate n) * (1 / 4 : ℝ) := hscaled
    _ = linearSingletonRate n (standardMutationRate n) / 4 := by ring

/-- The coefficient-independent pointwise drift inequality for positive ordered linear
functions.  This is the direct formal counterpart of the classical rank-potential lemma. -/
theorem classicalLinearDriftRate_mul_rankLinearPotential_le_drift_standard
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    classicalLinearDriftRate n * rankLinearPotential x ≤
      driftAt
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearPotential (n := n)) x := by
  have hnpos : 0 < n := by omega
  have hV0 : 0 ≤ rankLinearPotential x := rankLinearPotential_nonneg hnpos x
  have hrate := classicalLinearDriftRate_le_quarter_standardSingletonRate hn
  have hscale := mul_le_mul_of_nonneg_right hrate hV0
  exact hscale.trans
    (quarter_rate_mul_rankLinearPotential_le_drift_standard hn w hw hmono x)

/-- Mutation masks outside the already-accounted-for zero-singleton events. -/
def rankLinearRemainderMasks {n : ℕ} (x : BitString n) : Finset (MutationMask n) :=
  Finset.univ \ zeroSingletonMasks x

/-- Aggregate contribution of all non-zero-singleton masks to one-step rank drift. -/
noncomputable def rankLinearRemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ rankLinearRemainderMasks x,
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/-- Exact decomposition of rank drift into the proved singleton term and one remainder. -/
theorem rankLinear_drift_eq_singleton_add_remainder
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (rankLinearPotential (n := n)) x =
      linearSingletonRate n p * rankLinearPotential x +
        rankLinearRemainderContribution p w x := by
  rw [rankLinear_drift_eq_mask_sum]
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))
  change (∑ mask : MutationMask n, F mask) =
    linearSingletonRate n p * rankLinearPotential x +
      rankLinearRemainderContribution p w x
  have hsubset : zeroSingletonMasks x ⊆
      (Finset.univ : Finset (MutationMask n)) := Finset.subset_univ _
  have hsplit := Finset.sum_sdiff (f := F) hsubset
  have hsum :
      (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ rankLinearRemainderMasks x, F mask) := by
    change (∑ mask : MutationMask n, F mask) =
      (∑ mask ∈ zeroSingletonMasks x, F mask) +
        (∑ mask ∈ ((Finset.univ : Finset (MutationMask n)) \ zeroSingletonMasks x), F mask)
    simpa only [add_comm] using hsplit.symm
  calc
    (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ rankLinearRemainderMasks x, F mask) := hsum
    _ = linearSingletonRate n p * rankLinearPotential x +
        rankLinearRemainderContribution p w x := by
      have hsingle :
          (∑ mask ∈ zeroSingletonMasks x, F mask) =
            linearSingletonRate n p * rankLinearPotential x := by
        simpa [F] using
          (rankLinear_zeroSingleton_contribution_eq (p := p) w hw x)
      rw [hsingle]
      rfl

/--
Legacy residual inequality after removing the singleton contribution.  The direct Stage-13
C1/C2/C3 assembly no longer needs this interface, but it remains a useful exact alternative
decomposition and compatibility theorem.
-/
def HasClassicalLinearRankRemainderBound {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ x : BitString n, 0 < rankLinearPotential x →
    classicalLinearDriftRate n * rankLinearPotential x -
        linearSingletonRate n (standardMutationRate n) * rankLinearPotential x ≤
      rankLinearRemainderContribution (standardMutationRate n) w x

/-- A bound on the non-singleton remainder immediately yields the classical rank drift. -/
theorem hasClassicalLinearRankDrift_of_remainder_bound
    {n : ℕ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hrem : HasClassicalLinearRankRemainderBound w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (standardMutationRate n) (linearFitness w))
      (rankLinearPotential (n := n))
      (classicalLinearDriftRate n) := by
  intro x hx
  rw [rankLinear_drift_eq_singleton_add_remainder w hw x]
  have hr := hrem x hx
  linarith

/--
Named coefficient-independent rank-drift property for the classical linear-function
analysis.  Stage 13 proves this proposition for positive nonincreasing linear weights,
while the name continues to separate the combinatorial EA argument from the generic
multiplicative-drift theorem.
-/
def HasClassicalLinearRankDrift {n : ℕ} (w : Fin n → ℝ) : Prop :=
  HasMultiplicativeDriftLowerBound
    (onePlusOneTransition (standardMutationRate n) (linearFitness w))
    (rankLinearPotential (n := n))
    (classicalLinearDriftRate n)

/-- Positive nonincreasing linear weights satisfy the classical coefficient-independent
rank-drift condition at the standard mutation rate. -/
theorem classicalLinearRankDrift
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasClassicalLinearRankDrift w := by
  unfold HasClassicalLinearRankDrift HasMultiplicativeDriftLowerBound
  intro x _hx
  exact classicalLinearDriftRate_mul_rankLinearPotential_le_drift_standard
    hn w hw hmono x

/-- The named classical drift property follows directly from the remainder inequality. -/
theorem classicalLinearRankDrift_of_remainder_bound
    {n : ℕ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hrem : HasClassicalLinearRankRemainderBound w) :
    HasClassicalLinearRankDrift w := by
  simpa [HasClassicalLinearRankDrift] using
    (hasClassicalLinearRankDrift_of_remainder_bound w hw hrem)

/--
Once the classical pointwise rank-drift lemma is established, the generic
multiplicative-drift theorem immediately gives an unrestricted runtime bound.
-/
theorem linear_runtimeSup_le_of_classical_rank_drift
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hdrift : HasClassicalLinearRankDrift w) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          (classicalLinearDriftRate n) 1 (rankLinearPotential (n := n)) x) := by
  have hnpos : 0 < n := by omega
  have hp := standardMutationRate_mem_unitInterval_linear hn
  have hP : IsStochastic
      (onePlusOneTransition (standardMutationRate n) (linearFitness w)) :=
    onePlusOneTransition_stochastic hp.1 hp.2 (linearFitness w)
  have hbound := multiplicativeDrift_runtimeSup_le
    (onePlusOneTransition (standardMutationRate n) (linearFitness w))
    (rankLinearPotential (n := n))
    (classicalLinearDriftRate n) 1
    hP (classicalLinearDriftRate_pos hnpos) (by norm_num)
    (rankLinearPotential_nonneg hnpos)
    (fun z hz => by
      exact one_le_rankLinearPotential_of_not_target hnpos z (by
        simpa [rankLinearTarget] using hz))
    (by simpa [HasClassicalLinearRankDrift] using hdrift) x
  calc
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) x =
      runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (realPotentialTarget (rankLinearPotential (n := n))) x := by
          symm
          exact runtimeSup_congr_target
            (onePlusOneTransition (standardMutationRate n) (linearFitness w))
            (realPotentialTarget (rankLinearPotential (n := n)))
            (rankLinearTarget n) rfl x
    _ ≤ ENNReal.ofReal
        (multiplicativeDriftRuntime
          (classicalLinearDriftRate n) 1 (rankLinearPotential (n := n)) x) := hbound

/--
The multiplicative-drift certificate for the rank potential is at most the textbook
`4 e n (1 + log(2n))` expression.  This isolates the deterministic endgame of the
classical linear-functions proof from the remaining stochastic drift lemma.
-/
theorem rankLinear_multiplicativeRuntime_le_log_bound
    {n : ℕ} (hn : 2 ≤ n) (x : BitString n) :
    multiplicativeDriftRuntime
        (classicalLinearDriftRate n) 1 (rankLinearPotential (n := n)) x ≤
      (4 * Real.exp 1 * (n : ℝ)) *
        (1 + Real.log (2 * (n : ℝ))) := by
  have hnpos : 0 < n := by omega
  let V := rankLinearPotential (n := n)
  let C : ℝ := 4 * Real.exp 1 * (n : ℝ)
  have hCpos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) (by exact_mod_cast hnpos)
  change multiplicativeDriftRuntime (classicalLinearDriftRate n) 1 V x ≤
    C * (1 + Real.log (2 * (n : ℝ)))
  by_cases hx0 : V x = 0
  · have hcert : multiplicativeDriftRuntime
        (classicalLinearDriftRate n) 1 V x = 0 := by
      unfold multiplicativeDriftRuntime additiveDriftRuntime
      simp [multiplicativeDriftPotential, hx0]
    rw [hcert]
    have htwo : (1 : ℝ) ≤ 2 * (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith
    have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg htwo
    exact mul_nonneg hCpos.le (by linarith)
  · have hxpos : 0 < V x := by
      have hnonneg : 0 ≤ V x := by
        dsimp [V]
        exact rankLinearPotential_nonneg hnpos x
      exact lt_of_le_of_ne hnonneg (Ne.symm hx0)
    have hVupper : V x ≤ 2 * (n : ℝ) := by
      dsimp [V]
      exact rankLinearPotential_le_two_mul_n x
    have hlog : Real.log (V x) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log hxpos hVupper
    have hcert : multiplicativeDriftRuntime
        (classicalLinearDriftRate n) 1 V x =
          C * (1 + Real.log (V x)) := by
      have hraw := multiplicativeDriftRuntime_eq_log_ratio
        V (classicalLinearDriftRate n) 1 (by norm_num) x hx0
      rw [hraw]
      simp [classicalLinearDriftRate, C]
    rw [hcert]
    exact mul_le_mul_of_nonneg_left (by linarith) hCpos.le

/-- Conditional end-to-end `O(n log n)` bound for ordered linear functions. -/
theorem linear_runtimeSup_le_log_bound_of_classical_rank_drift
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hdrift : HasClassicalLinearRankDrift w) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) x ≤
      ENNReal.ofReal
        ((4 * Real.exp 1 * (n : ℝ)) *
          (1 + Real.log (2 * (n : ℝ)))) := by
  have hrun := linear_runtimeSup_le_of_classical_rank_drift hn w hdrift x
  exact hrun.trans (ENNReal.ofReal_le_ofReal
    (rankLinear_multiplicativeRuntime_le_log_bound hn x))

/-- Unconditional coefficient-independent `O(n log n)` runtime bound for positive
nonincreasing linear functions under standard bit mutation. -/
theorem linear_runtimeSup_le_log_bound
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) x ≤
      ENNReal.ofReal
        ((4 * Real.exp 1 * (n : ℝ)) *
          (1 + Real.log (2 * (n : ℝ)))) := by
  exact linear_runtimeSup_le_log_bound_of_classical_rank_drift
    hn w (classicalLinearRankDrift hn w hw hmono) x


/-! ### Stage 14: consolidated all-ones and finite-horizon endpoints -/

/-- In positive dimension the rank target is the same canonical all-ones target used by
OneMax.  The latter has a computable target-membership instance and is convenient for public
runtime statements. -/
theorem rankLinearTarget_eq_oneMaxTarget {n : ℕ} (hn : 0 < n) :
    rankLinearTarget n = oneMaxTarget n := by
  rw [rankLinearTarget_eq_singleton hn, oneMaxTarget_eq_singleton]

/--
Every finite Bellman truncation for the ordered linear `(1+1)` EA obeys the same
coefficient-independent logarithmic bound as `runtimeSup`.  This statement stays entirely
inside the finite-state semantics and therefore does not require the future sample-path
monotone-convergence bridge.
-/
theorem linear_finiteHorizonRuntime_le_log_bound
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (horizon : ℕ) (x : BitString n) :
    finiteHorizonRuntime
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) horizon x ≤
      (4 * Real.exp 1 * (n : ℝ)) *
        (1 + Real.log (2 * (n : ℝ))) := by
  have hnpos : 0 < n := by omega
  have hp := standardMutationRate_mem_unitInterval_linear hn
  have hP : IsStochastic
      (onePlusOneTransition (standardMutationRate n) (linearFitness w)) :=
    onePlusOneTransition_stochastic hp.1 hp.2 (linearFitness w)
  have hfinite := multiplicativeDrift_finiteHorizonBound
    (onePlusOneTransition (standardMutationRate n) (linearFitness w))
    (rankLinearPotential (n := n))
    (classicalLinearDriftRate n) 1
    hP (classicalLinearDriftRate_pos hnpos) (by norm_num)
    (rankLinearPotential_nonneg hnpos)
    (fun z hz => by
      exact one_le_rankLinearPotential_of_not_target hnpos z (by
        simpa [rankLinearTarget] using hz))
    (by simpa [HasClassicalLinearRankDrift] using
      (classicalLinearRankDrift hn w hw hmono))
  have hcert :
      finiteHorizonRuntime
          (onePlusOneTransition (standardMutationRate n) (linearFitness w))
          (rankLinearTarget n) horizon x ≤
        multiplicativeDriftRuntime
          (classicalLinearDriftRate n) 1 (rankLinearPotential (n := n)) x := by
    calc
      finiteHorizonRuntime
          (onePlusOneTransition (standardMutationRate n) (linearFitness w))
          (rankLinearTarget n) horizon x =
        finiteHorizonRuntime
          (onePlusOneTransition (standardMutationRate n) (linearFitness w))
          (realPotentialTarget (rankLinearPotential (n := n))) horizon x := by
            exact finiteHorizonRuntime_congr_target
              (onePlusOneTransition (standardMutationRate n) (linearFitness w))
              (rankLinearTarget n)
              (realPotentialTarget (rankLinearPotential (n := n))) rfl horizon x
      _ ≤ multiplicativeDriftRuntime
          (classicalLinearDriftRate n) 1 (rankLinearPotential (n := n)) x :=
        hfinite horizon x
  exact hcert.trans (rankLinear_multiplicativeRuntime_le_log_bound hn x)

/--
The finite-horizon theorem stated for the canonical OneMax target, which is exactly the
singleton `{allOnes n}`.  This makes the optimization target explicit without exposing the
auxiliary rank potential in the theorem statement.
-/
theorem linear_finiteHorizonRuntime_allOnes_le_log_bound
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (horizon : ℕ) (x : BitString n) :
    finiteHorizonRuntime
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) horizon x ≤
      (4 * Real.exp 1 * (n : ℝ)) *
        (1 + Real.log (2 * (n : ℝ))) := by
  have hnpos : 0 < n := by omega
  calc
    finiteHorizonRuntime
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) horizon x =
      finiteHorizonRuntime
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) horizon x := by
          exact finiteHorizonRuntime_congr_target
            (onePlusOneTransition (standardMutationRate n) (linearFitness w))
            (oneMaxTarget n) (rankLinearTarget n)
            (rankLinearTarget_eq_oneMaxTarget hnpos).symm horizon x
    _ ≤ (4 * Real.exp 1 * (n : ℝ)) *
        (1 + Real.log (2 * (n : ℝ))) :=
      linear_finiteHorizonRuntime_le_log_bound hn w hw hmono horizon x

/--
The unrestricted Bellman runtime theorem stated for the canonical all-ones target rather
than through the zero set of the auxiliary rank potential.
-/
theorem linear_runtimeSup_allOnes_le_log_bound
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        ((4 * Real.exp 1 * (n : ℝ)) *
          (1 + Real.log (2 * (n : ℝ)))) := by
  have hnpos : 0 < n := by omega
  calc
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x =
      runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (rankLinearTarget n) x := by
          exact runtimeSup_congr_target
            (onePlusOneTransition (standardMutationRate n) (linearFitness w))
            (oneMaxTarget n) (rankLinearTarget n)
            (rankLinearTarget_eq_oneMaxTarget hnpos).symm x
    _ ≤ ENNReal.ofReal
        ((4 * Real.exp 1 * (n : ℝ)) *
          (1 + Real.log (2 * (n : ℝ)))) :=
      linear_runtimeSup_le_log_bound hn w hw hmono x

/-- The unrestricted all-ones runtime supremum is finite. -/
theorem linear_runtimeSup_allOnes_ne_top
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≠ ⊤ := by
  have hle := linear_runtimeSup_allOnes_le_log_bound hn w hw hmono x
  exact ne_top_of_le_ne_top (by simp) hle

end ECRuntime
