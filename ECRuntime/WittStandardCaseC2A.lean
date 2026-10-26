import ECRuntime.WittStandardCaseC3
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 33: exact localization of the remaining Witt C2A branch

Stage 32 closes the complete C3 contribution and reduces the sharp standard-rate
one-step theorem to `HasWittStandardCaseC2RemainderNonnegativity`.  Stage 31 already
shows that every accepted C2B equal-weight swap has zero Witt-potential drop.

This module isolates the genuinely nontrivial part of C2 without yet attempting the
conditional geometric estimate from Witt's Subcase 2.2.2.  The reduction is exact:

* accepted C2 masks are localized by their unique zero-to-one coordinate `i`;
* the localized contribution splits into the existing `A_i` and `B_i` classes;
* the `B_i` contribution is zero;
* the singleton `{i}` is removed exactly from `A_i`, leaving a local non-singleton
  remainder;
* an accepted `A_i` mask containing a worsening coordinate with objective weight
  equal to `w i` is forced to be the two-bit pair `{i,j}` and has zero Witt drop;
* consequently the complete Stage-32 C2 remainder is a sum of contributions from
  accepted non-singleton `A_i` masks all of whose worsening objective coefficients are
  strictly smaller than `w i`.

The last class is precisely the repository-convention form of Witt's difficult
Subcase 2.2.2.  The next stage can therefore focus only on the finite geometric
conditioning/cancellation for this strict tail.
-/

/-- Witt contribution of accepted C2 masks localized at their unique improving
coordinate `i`. -/
noncomputable def wittStandardCaseC2AtContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AtAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Accepted `A_i` contribution for the Witt potential. -/
noncomputable def wittStandardCaseC2AContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Accepted `B_i` contribution for the Witt potential. -/
noncomputable def wittStandardCaseC2BContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2BAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- The localized accepted C2 contribution is exactly `A_i + B_i`. -/
theorem wittStandardCaseC2AtContribution_eq_A_add_B {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AtContribution p w x i =
      wittStandardCaseC2AContribution p w x i +
        wittStandardCaseC2BContribution p w x i := by
  classical
  unfold wittStandardCaseC2AtContribution wittStandardCaseC2AContribution
    wittStandardCaseC2BContribution
  rw [classicalLinearCaseC2AtAcceptedMasks_eq_A_union_B w x i]
  exact Finset.sum_union (classicalLinearCaseC2AAcceptedMasks_disjoint_B w x i)

/-- The complete accepted `B_i` contribution is zero for the refined Witt potential. -/
theorem wittStandardCaseC2BContribution_eq_zero {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    wittStandardCaseC2BContribution p w x i = 0 := by
  unfold wittStandardCaseC2BContribution
  apply Finset.sum_eq_zero
  intro mask hmask
  have hdata := (mem_classicalLinearCaseC2BAcceptedMasks w x i mask).mp hmask
  rw [wittStandardLinearPotential_selected_drop_eq_zero_of_caseC2B
    w hw hmono x mask i hdata.1]
  ring

/-- Rejected C2 masks have zero selected Witt drop, so the raw C2 sum may be
restricted exactly to accepted C2 masks before localization. -/
theorem wittStandardCaseC2Contribution_eq_accepted {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittStandardCaseC2Contribution p w x =
      ∑ mask ∈ classicalLinearCaseC2AcceptedMasks w x,
        mutationMaskWeight p mask *
          (wittStandardLinearPotential w x -
            wittStandardLinearPotential w
              (selectedAfterMask (linearFitness w) x mask)) := by
  classical
  unfold wittStandardCaseC2Contribution classicalLinearCaseC2AcceptedMasks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp [hacc]
  · rw [wittStandardLinearPotential_selected_drop_of_rejects w x mask hacc]
    simp [hacc]

/-- The full C2 Witt contribution partitions by the unique currently-zero coordinate
that flips to one. -/
theorem wittStandardCaseC2Contribution_eq_sum_zeroPositions_at {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittStandardCaseC2Contribution p w x =
      ∑ i ∈ zeroPositions x, wittStandardCaseC2AtContribution p w x i := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
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
  rw [wittStandardCaseC2Contribution_eq_accepted p w x]
  unfold wittStandardCaseC2AtContribution
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

/-- Since `B_i` is zero, C2 is exactly the sum of the accepted `A_i` contributions. -/
theorem wittStandardCaseC2Contribution_eq_sum_zeroPositions_A {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittStandardCaseC2Contribution p w x =
      ∑ i ∈ zeroPositions x, wittStandardCaseC2AContribution p w x i := by
  rw [wittStandardCaseC2Contribution_eq_sum_zeroPositions_at]
  apply Finset.sum_congr rfl
  intro i hi
  rw [wittStandardCaseC2AtContribution_eq_A_add_B,
    wittStandardCaseC2BContribution_eq_zero p w hw hmono x i]
  ring

/-! ### Removing the already-accounted-for singleton locally -/

/-- Accepted `A_i` masks other than the singleton improvement `{i}`. -/
noncomputable def wittStandardCaseC2ANonSingletonAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) :=
  (classicalLinearCaseC2AAcceptedMasks w x i).erase ({i} : MutationMask n)

/-- Contribution of the accepted non-singleton `A_i` masks. -/
noncomputable def wittStandardCaseC2ANonSingletonContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- The local accepted `A_i` contribution is exactly its singleton term plus the
non-singleton remainder. -/
theorem wittStandardCaseC2AContribution_eq_singleton_add_nonSingleton {n : ℕ}
    {p : ℝ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AContribution p w x i =
      linearSingletonRate n p * wittStandardPotentialWeight w i +
        wittStandardCaseC2ANonSingletonContribution p w x i := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))
  have hsingle :
      ({i} : MutationMask n) ∈ classicalLinearCaseC2AAcceptedMasks w x i :=
    singleton_mem_classicalLinearCaseC2AAcceptedMasks w hw x i hi
  have hsum := Finset.sum_erase_add
    (classicalLinearCaseC2AAcceptedMasks w x i) F hsingle
  have hF :
      F ({i} : MutationMask n) =
        linearSingletonRate n p * wittStandardPotentialWeight w i := by
    dsimp [F]
    rw [mutationMaskWeight_singleton,
      wittStandardLinearPotential_selected_single_zero_flip_drop w hw x i hi]
    rfl
  unfold wittStandardCaseC2AContribution
    wittStandardCaseC2ANonSingletonContribution
    wittStandardCaseC2ANonSingletonAcceptedMasks
  change (∑ mask ∈ classicalLinearCaseC2AAcceptedMasks w x i, F mask) =
    linearSingletonRate n p * wittStandardPotentialWeight w i +
      ∑ mask ∈ (classicalLinearCaseC2AAcceptedMasks w x i).erase
        ({i} : MutationMask n), F mask
  rw [← hF]
  simpa only [add_comm] using hsum.symm

/-- Local C2A remainder after subtracting the singleton contribution at coordinate `i`. -/
noncomputable def wittStandardCaseC2ALocalRemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  wittStandardCaseC2AContribution p w x i -
    linearSingletonRate n p * wittStandardPotentialWeight w i

/-- At a currently-zero coordinate, the local remainder is exactly the accepted
non-singleton `A_i` contribution. -/
theorem wittStandardCaseC2ALocalRemainder_eq_nonSingleton {n : ℕ}
    {p : ℝ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2ALocalRemainderContribution p w x i =
      wittStandardCaseC2ANonSingletonContribution p w x i := by
  unfold wittStandardCaseC2ALocalRemainderContribution
  rw [wittStandardCaseC2AContribution_eq_singleton_add_nonSingleton w hw x i hi]
  ring

/-- The complete C2 remainder is the sum of the local `A_i` remainders. -/
theorem wittStandardCaseC2RemainderContribution_eq_sum_localA {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittStandardCaseC2RemainderContribution p w x =
      ∑ i ∈ zeroPositions x,
        wittStandardCaseC2ALocalRemainderContribution p w x i := by
  unfold wittStandardCaseC2RemainderContribution
    wittStandardCaseC2ALocalRemainderContribution
  rw [wittStandardCaseC2Contribution_eq_sum_zeroPositions_A p w hw hmono x,
    wittStandardLinearPotential_eq_sum_zeroPositions, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

/-- Equivalently, the complete C2 remainder is the sum of accepted non-singleton
`A_i` contributions. -/
theorem wittStandardCaseC2RemainderContribution_eq_sum_nonSingletonA {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittStandardCaseC2RemainderContribution p w x =
      ∑ i ∈ zeroPositions x,
        wittStandardCaseC2ANonSingletonContribution p w x i := by
  rw [wittStandardCaseC2RemainderContribution_eq_sum_localA p w hw hmono x]
  apply Finset.sum_congr rfl
  intro i hi
  have hxi : x i = false := (mem_zeroPositions x i).mp hi
  exact wittStandardCaseC2ALocalRemainder_eq_nonSingleton w hw x i hxi

/-! ### Equal-weight `A_i` masks are another zero branch -/

/-- If an accepted localized C2 mutation contains a worsening flip whose objective
weight equals the improving weight, positivity forces the mutation to be exactly that
pair.  This statement does not depend on whether the worsening coordinate lies to the
left or right of `i`. -/
theorem accepted_caseC2At_eq_equalWeight_pair_of_bad_equal {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i j : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask))
    (hj : j ∈ oneToZeroFlips x mask) (hwji : w j = w i) :
    oneToZeroFlips x mask = {j} ∧ mask = {i, j} := by
  have hzero : zeroToOneFlips x mask = {i} := hAt
  have hbalance := (accepts_linearFitness_iff_flip_sums w x mask).mp hacc
  rw [hzero] at hbalance
  simp at hbalance
  have hwj_le_sum :
      w j ≤ ∑ k ∈ oneToZeroFlips x mask, w k :=
    Finset.single_le_sum (fun k hk => (hw k).le) hj
  have hsum_le_wi : (∑ k ∈ oneToZeroFlips x mask, w k) ≤ w i := by
    simpa using hbalance
  have hsum_eq_wj : (∑ k ∈ oneToZeroFlips x mask, w k) = w j := by
    apply le_antisymm
    · simpa [hwji] using hsum_le_wi
    · exact hwj_le_sum
  have hone : oneToZeroFlips x mask = {j} := by
    ext k
    simp only [Finset.mem_singleton]
    constructor
    · intro hk
      by_contra hkj
      have hkErase : k ∈ (oneToZeroFlips x mask).erase j :=
        Finset.mem_erase.mpr ⟨hkj, hk⟩
      have hsumErase := Finset.sum_erase_add (oneToZeroFlips x mask) w hj
      have hsumEraseZero : (∑ l ∈ (oneToZeroFlips x mask).erase j, w l) = 0 := by
        rw [hsum_eq_wj] at hsumErase
        linarith
      have hwk_le : w k ≤ ∑ l ∈ (oneToZeroFlips x mask).erase j, w l :=
        Finset.single_le_sum (fun l hl => (hw l).le) hkErase
      rw [hsumEraseZero] at hwk_le
      exact (not_le_of_gt (hw k)) hwk_le
    · intro hkj
      subst k
      exact hj
  have hiMask : i ∈ mask := mem_mask_of_classicalLinearCaseC2At x mask i hAt
  have hjMask : j ∈ mask := ((mem_oneToZeroFlips x mask j).mp hj).1
  have hmaskPair : mask = {i, j} := by
    ext k
    constructor
    · intro hk
      cases hxk : x k with
      | false =>
          have hkPos : k ∈ zeroToOneFlips x mask :=
            (mem_zeroToOneFlips x mask k).2 ⟨hk, hxk⟩
          rw [hzero] at hkPos
          have hki : k = i := by simpa using hkPos
          simp [hki]
      | true =>
          have hkNeg : k ∈ oneToZeroFlips x mask :=
            (mem_oneToZeroFlips x mask k).2 ⟨hk, hxk⟩
          rw [hone] at hkNeg
          have hkj : k = j := by simpa using hkNeg
          simp [hkj]
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hki | hkj
      · simpa [hki] using hiMask
      · simpa [hkj] using hjMask
  exact ⟨hone, hmaskPair⟩

/-- Hence an accepted localized C2 mutation with an equal-weight worsening coordinate
has exactly zero Witt-potential drop. -/
theorem wittStandardLinearPotential_selected_drop_eq_zero_of_caseC2At_equal_bad
    {n : ℕ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i j : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask))
    (hj : j ∈ oneToZeroFlips x mask) (hwji : w j = w i) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  rcases accepted_caseC2At_eq_equalWeight_pair_of_bad_equal
    w hw x mask i j hAt hacc hj hwji with ⟨hone, _hmask⟩
  rw [wittStandardLinearPotential_selected_drop_of_accepts w x mask hacc,
    flipContribution_sum_eq_flip_sums, hAt, hone]
  simp only [Finset.sum_singleton]
  rw [wittStandardPotentialWeight_eq_of_weight_eq w hwji]
  ring

/-- Equal-weight accepted non-singleton `A_i` masks. -/
noncomputable def wittStandardCaseC2AEqualAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) :=
  (wittStandardCaseC2ANonSingletonAcceptedMasks w x i).filter (fun mask =>
    ∃ j ∈ oneToZeroFlips x mask, w j = w i)

/-- Strict-tail accepted non-singleton `A_i` masks: every worsening objective
coefficient is strictly smaller than the improving coefficient. -/
noncomputable def wittStandardCaseC2AStrictAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) :=
  (wittStandardCaseC2ANonSingletonAcceptedMasks w x i).filter (fun mask =>
    ∀ j ∈ oneToZeroFlips x mask, w j < w i)

@[simp] theorem mem_wittStandardCaseC2AEqualAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AEqualAcceptedMasks w x i ↔
      mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i ∧
        ∃ j ∈ oneToZeroFlips x mask, w j = w i := by
  classical
  simp [wittStandardCaseC2AEqualAcceptedMasks]

@[simp] theorem mem_wittStandardCaseC2AStrictAcceptedMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i ↔
      mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i ∧
        ∀ j ∈ oneToZeroFlips x mask, w j < w i := by
  classical
  simp [wittStandardCaseC2AStrictAcceptedMasks]

/-- Membership in the non-singleton `A_i` set recovers both accepted `A_i` data and
inequality with the singleton mask. -/
theorem mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i ↔
      mask ∈ classicalLinearCaseC2AAcceptedMasks w x i ∧
        mask ≠ ({i} : MutationMask n) := by
  classical
  simp [wittStandardCaseC2ANonSingletonAcceptedMasks, and_comm]

/-- A non-singleton localized C2 mask has at least one worsening flip. -/
theorem oneToZeroFlips_nonempty_of_caseC2At_of_ne_singleton {n : ℕ}
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hAt : IsClassicalLinearCaseC2At x mask i)
    (hne : mask ≠ ({i} : MutationMask n)) :
    (oneToZeroFlips x mask).Nonempty := by
  by_contra hempty
  have honeEmpty : oneToZeroFlips x mask = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact hempty ⟨j, hj⟩
  apply hne
  ext k
  constructor
  · intro hk
    cases hxk : x k with
    | false =>
        have hkPos : k ∈ zeroToOneFlips x mask :=
          (mem_zeroToOneFlips x mask k).2 ⟨hk, hxk⟩
        rw [hAt] at hkPos
        simpa using hkPos
    | true =>
        have hkNeg : k ∈ oneToZeroFlips x mask :=
          (mem_oneToZeroFlips x mask k).2 ⟨hk, hxk⟩
        rw [honeEmpty] at hkNeg
        simp at hkNeg
  · intro hk
    have hki : k = i := by simpa using hk
    subst k
    exact mem_mask_of_classicalLinearCaseC2At x mask i hAt

/-- Under nonincreasing objective weights, the accepted non-singleton `A_i` class is
exactly the disjoint union of the equal-weight zero branch and the strict-tail branch. -/
theorem wittStandardCaseC2ANonSingletonAcceptedMasks_eq_equal_union_strict
    {n : ℕ} (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    wittStandardCaseC2ANonSingletonAcceptedMasks w x i =
      wittStandardCaseC2AEqualAcceptedMasks w x i ∪
        wittStandardCaseC2AStrictAcceptedMasks w x i := by
  classical
  ext mask
  constructor
  · intro hmask
    have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
      w x i mask).mp hmask
    have hA := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
    by_cases heq : ∃ j ∈ oneToZeroFlips x mask, w j = w i
    · exact Finset.mem_union.mpr (Or.inl
        ((mem_wittStandardCaseC2AEqualAcceptedMasks w x i mask).2 ⟨hmask, heq⟩))
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).2
      refine ⟨hmask, ?_⟩
      intro j hj
      have hij : i.val < j.val :=
        index_lt_of_mem_oneToZero_of_caseC2A x mask i j hA.1 hj
      have hwle : w j ≤ w i := hmono i j (Nat.le_of_lt hij)
      have hwne : w j ≠ w i := by
        intro hji
        exact heq ⟨j, hj, hji⟩
      exact lt_of_le_of_ne hwle hwne
  · intro hmask
    rcases Finset.mem_union.mp hmask with heq | hstrict
    · exact ((mem_wittStandardCaseC2AEqualAcceptedMasks w x i mask).mp heq).1
    · exact ((mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hstrict).1

/-- The equal and strict non-singleton `A_i` classes are disjoint. -/
theorem wittStandardCaseC2AEqualAcceptedMasks_disjoint_strict {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    Disjoint (wittStandardCaseC2AEqualAcceptedMasks w x i)
      (wittStandardCaseC2AStrictAcceptedMasks w x i) := by
  classical
  rw [Finset.disjoint_left]
  intro mask heq hstrict
  have heqData := (mem_wittStandardCaseC2AEqualAcceptedMasks w x i mask).mp heq
  have hstrictData := (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hstrict
  rcases heqData.2 with ⟨j, hj, hwji⟩
  have hlt := hstrictData.2 j hj
  linarith

/-- Aggregate equal-weight non-singleton `A_i` contribution. -/
noncomputable def wittStandardCaseC2AEqualContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AEqualAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Aggregate strict-tail non-singleton `A_i` contribution. -/
noncomputable def wittStandardCaseC2AStrictContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Every equal-weight non-singleton `A_i` term is zero, hence so is their sum. -/
theorem wittStandardCaseC2AEqualContribution_eq_zero {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AEqualContribution p w x i = 0 := by
  unfold wittStandardCaseC2AEqualContribution
  apply Finset.sum_eq_zero
  intro mask hmask
  have hdata := (mem_wittStandardCaseC2AEqualAcceptedMasks w x i mask).mp hmask
  have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
    w x i mask).mp hdata.1
  have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
  rcases hdata.2 with ⟨j, hj, hwji⟩
  rw [wittStandardLinearPotential_selected_drop_eq_zero_of_caseC2At_equal_bad
    w hw x mask i j hAdata.1.1 hAdata.2 hj hwji]
  ring

/-- After removing the equal-weight zero branch, the complete local non-singleton
`A_i` remainder is exactly the strict-tail contribution. -/
theorem wittStandardCaseC2ANonSingletonContribution_eq_strict {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2ANonSingletonContribution p w x i =
      wittStandardCaseC2AStrictContribution p w x i := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))
  unfold wittStandardCaseC2ANonSingletonContribution
    wittStandardCaseC2AStrictContribution
  change (∑ mask ∈ wittStandardCaseC2ANonSingletonAcceptedMasks w x i, F mask) =
    ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i, F mask
  rw [wittStandardCaseC2ANonSingletonAcceptedMasks_eq_equal_union_strict
    w hmono x i]
  rw [Finset.sum_union (wittStandardCaseC2AEqualAcceptedMasks_disjoint_strict
    w x i)]
  have heq :
      (∑ mask ∈ wittStandardCaseC2AEqualAcceptedMasks w x i, F mask) = 0 := by
    simpa only [F, wittStandardCaseC2AEqualContribution] using
      wittStandardCaseC2AEqualContribution_eq_zero p w hw x i
  rw [heq, zero_add]

/-- The complete Stage-32 C2 remainder is exactly the sum of strict-tail `A_i`
contributions over currently-zero improving coordinates. -/
theorem wittStandardCaseC2RemainderContribution_eq_sum_strictA {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittStandardCaseC2RemainderContribution p w x =
      ∑ i ∈ zeroPositions x, wittStandardCaseC2AStrictContribution p w x i := by
  rw [wittStandardCaseC2RemainderContribution_eq_sum_nonSingletonA
    p w hw hmono x]
  apply Finset.sum_congr rfl
  intro i hi
  exact wittStandardCaseC2ANonSingletonContribution_eq_strict
    p w hw hmono x i

/-! ### Final Stage-33 certificate -/

/-- The only remaining one-step certificate after the exact Stage-33 reductions. -/
def HasWittStandardStrictC2AContributionNonnegativity {n : ℕ}
    (w : Fin n → ℝ) : Prop :=
  ∀ (x : BitString n) (i : Fin n), x i = false →
    0 ≤ wittStandardCaseC2AStrictContribution
      (standardMutationRate n) w x i

/-- Pointwise nonnegativity of the strict-tail `A_i` contributions closes the complete
C2 remainder. -/
theorem hasWittStandardCaseC2RemainderNonnegativity_of_strictC2A
    {n : ℕ} (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (hstrict : HasWittStandardStrictC2AContributionNonnegativity w) :
    HasWittStandardCaseC2RemainderNonnegativity w := by
  intro x
  rw [wittStandardCaseC2RemainderContribution_eq_sum_strictA
    (standardMutationRate n) w hw hmono x]
  apply Finset.sum_nonneg
  intro i hi
  exact hstrict x i ((mem_zeroPositions x i).mp hi)

/-- Once the strict-tail C2A certificate is available, Stage 32 closes the full
non-singleton remainder. -/
theorem hasWittStandardRemainderNonnegativity_of_strictC2A
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (hstrict : HasWittStandardStrictC2AContributionNonnegativity w) :
    HasWittStandardRemainderNonnegativity w := by
  exact hasWittStandardRemainderNonnegativity_of_caseC2
    hn w hw hmono
      (hasWittStandardCaseC2RemainderNonnegativity_of_strictC2A
        w hw hmono hstrict)

/-- The Stage-33 strict-tail certificate is therefore sufficient for the sharp
`1/(e n)` multiplicative-drift interface. -/
theorem wittStandard_hasMultiplicativeDriftLowerBound_of_strictC2A
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (hstrict : HasWittStandardStrictC2AContributionNonnegativity w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (standardMutationRate n) (linearFitness w))
      (wittStandardLinearPotential w)
      (wittStandardLinearDriftRate n) := by
  exact wittStandard_hasMultiplicativeDriftLowerBound_of_remainder_nonnegative
    (by omega : 2 ≤ n) w hw
      (hasWittStandardRemainderNonnegativity_of_strictC2A
        hn w hw hmono hstrict)

end ECRuntime
