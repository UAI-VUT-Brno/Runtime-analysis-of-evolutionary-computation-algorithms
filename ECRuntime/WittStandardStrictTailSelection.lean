import ECRuntime.WittStandardStrictTailEnvelope
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 36: erase-closed strict-tail selection family

Stage 35 fix 1 compiler-promotes the sharp geometric envelope for the actual
state-dependent strict tail.  The remaining issue is selection: Stage 34 sums only
accepted non-singleton strict-tail `A_i` masks, whereas the elementary Bernoulli
calculation is most naturally performed on an erase-closed family that also contains
the singleton `{i}`.

This module makes that boundary explicit.  We adjoin the singleton by defining the
accepted strict closure directly, prove that erasing any worsening flip preserves the
closure, and recover the usual erase-pairing marginal inequality inside this family.
The selected strict bad mass is then rewritten as a coordinate sum of closure flip
masses and bounded by the Stage-35 geometric tail envelope.

The resulting estimate still contains the singleton boundary mass.  This is
intentional: coordinatewise erase pairing alone is not the final selected comparison.
The next proof slice must use an aggregate downward-closed-family argument rather than
silently discarding that boundary term.
-/

/-! ## The erase-closed strict family -/

/-- Accepted localized `A_i` masks for which every worsening flip has objective
coefficient strictly smaller than `w i`.  Unlike the Stage-33 strict family, this set
also contains the singleton `{i}` when `x i = false`; hence it is closed under erasing
worsening flips. -/
noncomputable def wittStandardCaseC2AStrictClosureMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) :=
  (classicalLinearCaseC2AAcceptedMasks w x i).filter (fun mask =>
    ∀ j ∈ oneToZeroFlips x mask, w j < w i)

@[simp] theorem mem_wittStandardCaseC2AStrictClosureMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AStrictClosureMasks w x i ↔
      mask ∈ classicalLinearCaseC2AAcceptedMasks w x i ∧
        ∀ j ∈ oneToZeroFlips x mask, w j < w i := by
  classical
  simp [wittStandardCaseC2AStrictClosureMasks]

/-- The Stage-33 strict accepted family is exactly the strict closure with its singleton
boundary removed. -/
theorem wittStandardCaseC2AStrictAcceptedMasks_eq_closure_erase_singleton {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AStrictAcceptedMasks w x i =
      (wittStandardCaseC2AStrictClosureMasks w x i).erase
        ({i} : MutationMask n) := by
  classical
  ext mask
  constructor
  · intro hmask
    have hstrict := (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hmask
    have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
      w x i mask).mp hstrict.1
    exact Finset.mem_erase.mpr ⟨hbase.2,
      (mem_wittStandardCaseC2AStrictClosureMasks w x i mask).2
        ⟨hbase.1, hstrict.2⟩⟩
  · intro hmask
    have herase := Finset.mem_erase.mp hmask
    have hclosure :=
      (mem_wittStandardCaseC2AStrictClosureMasks w x i mask).mp herase.2
    apply (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).2
    exact ⟨
      (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff w x i mask).2
        ⟨hclosure.1, herase.1⟩,
      hclosure.2
    ⟩

/-- At a currently-zero improving coordinate, the singleton boundary belongs to the
strict closure. -/
theorem singleton_mem_wittStandardCaseC2AStrictClosureMasks {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    ({i} : MutationMask n) ∈ wittStandardCaseC2AStrictClosureMasks w x i := by
  apply (mem_wittStandardCaseC2AStrictClosureMasks w x i
    ({i} : MutationMask n)).2
  refine ⟨singleton_mem_classicalLinearCaseC2AAcceptedMasks w hw x i hi, ?_⟩
  intro j hj
  have hjData := (mem_oneToZeroFlips x ({i} : MutationMask n) j).mp hj
  have hji : j = i := by
    simpa using hjData.1
  subst j
  simp [hi] at hjData

/-- Erasing a worsening flip from the strict closure stays in the strict closure. -/
theorem erase_oneToZero_mem_wittStandardCaseC2AStrictClosureMasks {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n) (j : Fin n)
    (hmask : mask ∈ wittStandardCaseC2AStrictClosureMasks w x i)
    (hj : j ∈ oneToZeroFlips x mask) :
    mask.erase j ∈ wittStandardCaseC2AStrictClosureMasks w x i := by
  have hdata := (mem_wittStandardCaseC2AStrictClosureMasks w x i mask).mp hmask
  have hjData := (mem_oneToZeroFlips x mask j).mp hj
  apply (mem_wittStandardCaseC2AStrictClosureMasks w x i (mask.erase j)).2
  refine ⟨erase_oneToZero_mem_classicalLinearCaseC2AAcceptedMasks
    w hw x i mask j hdata.1 hj, ?_⟩
  intro k hk
  rw [oneToZeroFlips_erase_of_true x mask j hjData.2] at hk
  exact hdata.2 k (Finset.mem_erase.mp hk).2

/-! ## Closure flip masses and erase pairing -/

/-- Strict-closure masks that flip a specified coordinate. -/
noncomputable def wittStandardCaseC2AStrictClosureWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : Finset (MutationMask n) :=
  (wittStandardCaseC2AStrictClosureMasks w x i).filter (fun mask => j ∈ mask)

/-- Strict-closure masks that do not flip a specified coordinate. -/
noncomputable def wittStandardCaseC2AStrictClosureWithoutFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : Finset (MutationMask n) :=
  (wittStandardCaseC2AStrictClosureMasks w x i).filter (fun mask => j ∉ mask)

@[simp] theorem mem_wittStandardCaseC2AStrictClosureWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AStrictClosureWithFlipAt w x i j ↔
      mask ∈ wittStandardCaseC2AStrictClosureMasks w x i ∧ j ∈ mask := by
  classical
  simp [wittStandardCaseC2AStrictClosureWithFlipAt]

@[simp] theorem mem_wittStandardCaseC2AStrictClosureWithoutFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AStrictClosureWithoutFlipAt w x i j ↔
      mask ∈ wittStandardCaseC2AStrictClosureMasks w x i ∧ j ∉ mask := by
  classical
  simp [wittStandardCaseC2AStrictClosureWithoutFlipAt]

/-- Total mutation mass of the erase-closed strict family. -/
noncomputable def wittStandardCaseC2AStrictClosureMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictClosureMasks w x i,
    mutationMaskWeight p mask

/-- Strict-closure mass among masks that flip coordinate `j`. -/
noncomputable def wittStandardCaseC2AStrictClosureFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictClosureWithFlipAt w x i j,
    mutationMaskWeight p mask

/-- Strict-closure mass among masks that do not flip coordinate `j`. -/
noncomputable def wittStandardCaseC2AStrictClosureWithoutFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictClosureWithoutFlipAt w x i j,
    mutationMaskWeight p mask

/-- Closure mass partitions according to whether `j` flips. -/
theorem wittStandardCaseC2AStrictClosureMass_eq_flipAt_add_withoutFlipAt {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) :
    wittStandardCaseC2AStrictClosureMass p w x i =
      wittStandardCaseC2AStrictClosureFlipAtMass p w x i j +
        wittStandardCaseC2AStrictClosureWithoutFlipAtMass p w x i j := by
  classical
  unfold wittStandardCaseC2AStrictClosureMass
    wittStandardCaseC2AStrictClosureFlipAtMass
    wittStandardCaseC2AStrictClosureWithoutFlipAtMass
    wittStandardCaseC2AStrictClosureWithFlipAt
    wittStandardCaseC2AStrictClosureWithoutFlipAt
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hj : j ∈ mask <;> simp [hj]

/-- Exact singleton-boundary decomposition of closure mass. -/
theorem wittStandardCaseC2AStrictClosureMass_eq_singleton_add_strictMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictClosureMass p w x i =
      linearSingletonRate n p +
        wittStandardCaseC2AStrictAcceptedMass p w x i := by
  have hsingle := singleton_mem_wittStandardCaseC2AStrictClosureMasks
    w hw x i hi
  have hsum := Finset.sum_erase_add
    (wittStandardCaseC2AStrictClosureMasks w x i)
    (mutationMaskWeight p) hsingle
  rw [← wittStandardCaseC2AStrictAcceptedMasks_eq_closure_erase_singleton]
    at hsum
  unfold wittStandardCaseC2AStrictClosureMass
    wittStandardCaseC2AStrictAcceptedMass
  rw [mutationMaskWeight_singleton] at hsum
  unfold linearSingletonRate
  linarith

/-- Strict-closure mass is nonnegative for a genuine mutation probability. -/
theorem wittStandardCaseC2AStrictClosureMass_nonneg {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    0 ≤ wittStandardCaseC2AStrictClosureMass p w x i := by
  unfold wittStandardCaseC2AStrictClosureMass
  apply Finset.sum_nonneg
  intro mask hmask
  exact mutationMaskWeight_nonneg hp0 hp1 mask

/-- Erase pairing inside the strict closure. -/
theorem one_sub_p_mul_wittStandardCaseC2AStrictClosureFlipAtMass_le {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i j : Fin n) (hxj : x j = true) :
    (1 - p) * wittStandardCaseC2AStrictClosureFlipAtMass p w x i j ≤
      p * wittStandardCaseC2AStrictClosureWithoutFlipAtMass p w x i j := by
  classical
  unfold wittStandardCaseC2AStrictClosureFlipAtMass
    wittStandardCaseC2AStrictClosureWithoutFlipAtMass
  rw [Finset.mul_sum, Finset.mul_sum]
  have herase_inj :
      Set.InjOn (fun mask : MutationMask n => mask.erase j)
        ↑(wittStandardCaseC2AStrictClosureWithFlipAt w x i j) := by
    intro a ha b hb hab
    have hja : j ∈ a :=
      ((mem_wittStandardCaseC2AStrictClosureWithFlipAt w x i j a).mp ha).2
    have hjb : j ∈ b :=
      ((mem_wittStandardCaseC2AStrictClosureWithFlipAt w x i j b).mp hb).2
    have hab' : a.erase j = b.erase j := by simpa using hab
    calc
      a = insert j (a.erase j) := (Finset.insert_erase hja).symm
      _ = insert j (b.erase j) := by rw [hab']
      _ = b := Finset.insert_erase hjb
  have himage_subset :
      (wittStandardCaseC2AStrictClosureWithFlipAt w x i j).image
          (fun mask : MutationMask n => mask.erase j) ⊆
        wittStandardCaseC2AStrictClosureWithoutFlipAt w x i j := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨mask, hmask, rfl⟩
    have hmaskData :=
      (mem_wittStandardCaseC2AStrictClosureWithFlipAt w x i j mask).mp hmask
    apply (mem_wittStandardCaseC2AStrictClosureWithoutFlipAt
      w x i j (mask.erase j)).2
    have hjbad : j ∈ oneToZeroFlips x mask :=
      (mem_oneToZeroFlips x mask j).2 ⟨hmaskData.2, hxj⟩
    exact ⟨erase_oneToZero_mem_wittStandardCaseC2AStrictClosureMasks
      w hw x i mask j hmaskData.1 hjbad, by simp⟩
  calc
    (∑ mask ∈ wittStandardCaseC2AStrictClosureWithFlipAt w x i j,
        (1 - p) * mutationMaskWeight p mask) =
      ∑ mask ∈ wittStandardCaseC2AStrictClosureWithFlipAt w x i j,
        p * mutationMaskWeight p (mask.erase j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hjmask : j ∈ mask :=
        ((mem_wittStandardCaseC2AStrictClosureWithFlipAt
          w x i j mask).mp hmask).2
      exact mutationMaskWeight_erase_balance p mask j hjmask
    _ = ∑ z ∈ (wittStandardCaseC2AStrictClosureWithFlipAt w x i j).image
          (fun mask : MutationMask n => mask.erase j),
        p * mutationMaskWeight p z := by
      symm
      exact Finset.sum_image herase_inj
    _ ≤ ∑ z ∈ wittStandardCaseC2AStrictClosureWithoutFlipAt w x i j,
        p * mutationMaskWeight p z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      intro z hz hnotImage
      exact mul_nonneg hp0 (mutationMaskWeight_nonneg hp0 hp1 z)

/-- Marginal flip mass bound inside the erase-closed strict family. -/
theorem wittStandardCaseC2AStrictClosureFlipAtMass_le_p_mul_closureMass {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i j : Fin n) (hxj : x j = true) :
    wittStandardCaseC2AStrictClosureFlipAtMass p w x i j ≤
      p * wittStandardCaseC2AStrictClosureMass p w x i := by
  have hpair := one_sub_p_mul_wittStandardCaseC2AStrictClosureFlipAtMass_le
    hp0 hp1 w hw x i j hxj
  have hpart := wittStandardCaseC2AStrictClosureMass_eq_flipAt_add_withoutFlipAt
    p w x i j
  calc
    wittStandardCaseC2AStrictClosureFlipAtMass p w x i j =
        (1 - p) * wittStandardCaseC2AStrictClosureFlipAtMass p w x i j +
          p * wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by ring
    _ ≤ p * wittStandardCaseC2AStrictClosureWithoutFlipAtMass p w x i j +
          p * wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by
      exact add_le_add_left hpair _
    _ = p * (wittStandardCaseC2AStrictClosureFlipAtMass p w x i j +
          wittStandardCaseC2AStrictClosureWithoutFlipAtMass p w x i j) := by ring
    _ = p * wittStandardCaseC2AStrictClosureMass p w x i := by rw [← hpart]

/-! ## Rewriting the selected strict bad mass through closure marginals -/

/-- Strict accepted masks that flip coordinate `j`. -/
noncomputable def wittStandardCaseC2AStrictAcceptedWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : Finset (MutationMask n) :=
  (wittStandardCaseC2AStrictAcceptedMasks w x i).filter (fun mask => j ∈ mask)

@[simp] theorem mem_wittStandardCaseC2AStrictAcceptedWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AStrictAcceptedWithFlipAt w x i j ↔
      mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i ∧ j ∈ mask := by
  classical
  simp [wittStandardCaseC2AStrictAcceptedWithFlipAt]

/-- Mutation mass of strict accepted masks that flip coordinate `j`. -/
noncomputable def wittStandardCaseC2AStrictFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictAcceptedWithFlipAt w x i j,
    mutationMaskWeight p mask

/-- For a currently-one coordinate and a currently-zero improving coordinate, adjoining
or removing the singleton boundary does not change the flip-at family. -/
theorem wittStandardCaseC2AStrictAcceptedWithFlipAt_eq_closureWithFlipAt {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n)
    (hi : x i = false) (hxj : x j = true) :
    wittStandardCaseC2AStrictAcceptedWithFlipAt w x i j =
      wittStandardCaseC2AStrictClosureWithFlipAt w x i j := by
  classical
  have hji : j ≠ i := by
    intro h
    subst j
    simp [hi] at hxj
  ext mask
  constructor
  · intro hmask
    have hdata :=
      (mem_wittStandardCaseC2AStrictAcceptedWithFlipAt w x i j mask).mp hmask
    have hstrict :=
      (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hdata.1
    have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
      w x i mask).mp hstrict.1
    exact (mem_wittStandardCaseC2AStrictClosureWithFlipAt w x i j mask).2
      ⟨(mem_wittStandardCaseC2AStrictClosureMasks w x i mask).2
          ⟨hbase.1, hstrict.2⟩, hdata.2⟩
  · intro hmask
    have hdata :=
      (mem_wittStandardCaseC2AStrictClosureWithFlipAt w x i j mask).mp hmask
    have hclosure :=
      (mem_wittStandardCaseC2AStrictClosureMasks w x i mask).mp hdata.1
    have hne : mask ≠ ({i} : MutationMask n) := by
      intro hm
      have : j ∈ ({i} : MutationMask n) := by simpa [hm] using hdata.2
      have : j = i := by simpa using this
      exact hji this
    apply (mem_wittStandardCaseC2AStrictAcceptedWithFlipAt w x i j mask).2
    exact ⟨
      (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).2
        ⟨(mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff w x i mask).2
            ⟨hclosure.1, hne⟩,
          hclosure.2⟩,
      hdata.2
    ⟩

/-- Hence the strict selected flip mass equals the closure flip mass on any currently-one
coordinate when `i` is currently zero. -/
theorem wittStandardCaseC2AStrictFlipAtMass_eq_closureFlipAtMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n)
    (hi : x i = false) (hxj : x j = true) :
    wittStandardCaseC2AStrictFlipAtMass p w x i j =
      wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by
  unfold wittStandardCaseC2AStrictFlipAtMass
    wittStandardCaseC2AStrictClosureFlipAtMass
  rw [wittStandardCaseC2AStrictAcceptedWithFlipAt_eq_closureWithFlipAt
    w x i j hi hxj]

/-- The selected strict bad mass is a coordinate sum of strict flip masses. -/
theorem wittStandardCaseC2AStrictBadMass_eq_sum_coordinate_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AStrictBadMass p w x i =
      ∑ j : Fin n,
        if x j = true then
          wittStandardPotentialWeight w j *
            wittStandardCaseC2AStrictFlipAtMass p w x i j
        else 0 := by
  classical
  unfold wittStandardCaseC2AStrictBadMass
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

/-- Outside the state-dependent strict tail, a currently-one coordinate has zero strict
accepted flip mass. -/
theorem wittStandardCaseC2AStrictFlipAtMass_eq_zero_of_not_lt {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i j : Fin n)
    (hxj : x j = true) (hnot : ¬ w j < w i) :
    wittStandardCaseC2AStrictFlipAtMass p w x i j = 0 := by
  unfold wittStandardCaseC2AStrictFlipAtMass
  apply Finset.sum_eq_zero
  intro mask hmask
  have hdata :=
    (mem_wittStandardCaseC2AStrictAcceptedWithFlipAt w x i j mask).mp hmask
  have hstrict :=
    (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hdata.1
  have hjbad : j ∈ oneToZeroFlips x mask :=
    (mem_oneToZeroFlips x mask j).2 ⟨hdata.2, hxj⟩
  exact (hnot (hstrict.2 j hjbad)).elim

/-- Restrict the coordinate bad-mass sum to the actual strict tail. -/
theorem wittStandardCaseC2AStrictBadMass_eq_sum_tail_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AStrictBadMass p w x i =
      ∑ j ∈ wittStandardStrictTailIndices w x i,
        wittStandardPotentialWeight w j *
          wittStandardCaseC2AStrictFlipAtMass p w x i j := by
  rw [wittStandardCaseC2AStrictBadMass_eq_sum_coordinate_flipMass]
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

/-- With `x i = false`, the strict selected bad mass can be computed entirely from
closure flip masses over the state-dependent strict tail. -/
theorem wittStandardCaseC2AStrictBadMass_eq_sum_tail_closureFlipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (hi : x i = false) :
    wittStandardCaseC2AStrictBadMass p w x i =
      ∑ j ∈ wittStandardStrictTailIndices w x i,
        wittStandardPotentialWeight w j *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by
  rw [wittStandardCaseC2AStrictBadMass_eq_sum_tail_flipMass]
  apply Finset.sum_congr rfl
  intro j hj
  have hjData := (mem_wittStandardStrictTailIndices w x i j).mp hj
  rw [wittStandardCaseC2AStrictFlipAtMass_eq_closureFlipAtMass
    p w x i j hi hjData.1]

/-! ## What coordinatewise closure pairing proves -/

/-- Coordinatewise erase pairing bounds the selected strict bad mass by the strict-tail
weight sum times `p` times the closure mass. -/
theorem wittStandardCaseC2AStrictBadMass_le_p_mul_tailWeight_mul_closureMass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictBadMass p w x i ≤
      p * (∑ j ∈ wittStandardStrictTailIndices w x i,
          wittStandardPotentialWeight w j) *
        wittStandardCaseC2AStrictClosureMass p w x i := by
  rw [wittStandardCaseC2AStrictBadMass_eq_sum_tail_closureFlipMass
    p w x i hi]
  calc
    (∑ j ∈ wittStandardStrictTailIndices w x i,
      wittStandardPotentialWeight w j *
        wittStandardCaseC2AStrictClosureFlipAtMass p w x i j) ≤
      ∑ j ∈ wittStandardStrictTailIndices w x i,
        wittStandardPotentialWeight w j *
          (p * wittStandardCaseC2AStrictClosureMass p w x i) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjData := (mem_wittStandardStrictTailIndices w x i j).mp hj
        have hflip := wittStandardCaseC2AStrictClosureFlipAtMass_le_p_mul_closureMass
          hp0 hp1 w hw x i j hjData.1
        exact mul_le_mul_of_nonneg_left hflip
          (wittStandardPotentialWeight_pos w j).le
    _ = (∑ j ∈ wittStandardStrictTailIndices w x i,
          wittStandardPotentialWeight w j) *
        (p * wittStandardCaseC2AStrictClosureMass p w x i) := by
      rw [Finset.sum_mul]
    _ = p * (∑ j ∈ wittStandardStrictTailIndices w x i,
          wittStandardPotentialWeight w j) *
        wittStandardCaseC2AStrictClosureMass p w x i := by
      ring

/-- At the standard rate, Stage 35 turns the coordinatewise closure estimate into a
geometric survival bound.  The remaining gap to the Stage-34 selected bad-mass target
is exactly the singleton boundary hidden inside `closureMass`. -/
theorem wittStandardCaseC2AStrictBadMass_le_good_survival_mul_closureMass
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictBadMass (standardMutationRate n) w x i ≤
      (wittStandardPotentialWeight w i *
        (1 - (1 - standardMutationRate n) ^
          (wittStandardStrictTailIndices w x i).card)) *
        wittStandardCaseC2AStrictClosureMass
          (standardMutationRate n) w x i := by
  have hp := standardMutationRate_mem_unitInterval_linear hn
  have hbad :=
    wittStandardCaseC2AStrictBadMass_le_p_mul_tailWeight_mul_closureMass
      hp.1 hp.2 w hw x i hi
  have hgeom := standardMutationRate_mul_sum_wittStandardStrictTailWeight_le_goodMass
    hn w hmono x i
  have hclosure := wittStandardCaseC2AStrictClosureMass_nonneg
    hp.1 hp.2 w x i
  calc
    wittStandardCaseC2AStrictBadMass (standardMutationRate n) w x i ≤
      standardMutationRate n *
          (∑ j ∈ wittStandardStrictTailIndices w x i,
            wittStandardPotentialWeight w j) *
        wittStandardCaseC2AStrictClosureMass
          (standardMutationRate n) w x i := hbad
    _ ≤ (wittStandardPotentialWeight w i *
          (1 - (1 - standardMutationRate n) ^
            (wittStandardStrictTailIndices w x i).card)) *
        wittStandardCaseC2AStrictClosureMass
          (standardMutationRate n) w x i :=
      mul_le_mul_of_nonneg_right hgeom hclosure

/-- Expanded singleton-boundary form of the Stage-36 estimate.  This theorem records
precisely why a coordinatewise marginal argument is insufficient for the final
selected comparison: the closure contains the singleton improvement in addition to the
strict non-singleton accepted mass. -/
theorem wittStandardCaseC2AStrictBadMass_le_good_survival_mul_singleton_add_strictMass
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictBadMass (standardMutationRate n) w x i ≤
      (wittStandardPotentialWeight w i *
        (1 - (1 - standardMutationRate n) ^
          (wittStandardStrictTailIndices w x i).card)) *
        (linearSingletonRate n (standardMutationRate n) +
          wittStandardCaseC2AStrictAcceptedMass
            (standardMutationRate n) w x i) := by
  rw [← wittStandardCaseC2AStrictClosureMass_eq_singleton_add_strictMass
    (standardMutationRate n) w hw x i hi]
  exact wittStandardCaseC2AStrictBadMass_le_good_survival_mul_closureMass
    hn w hw hmono x i hi

end ECRuntime
