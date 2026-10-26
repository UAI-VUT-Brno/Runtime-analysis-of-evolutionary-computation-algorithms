import ECRuntime.WittStandardStrictTailSelection
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 37: aggregate downset comparison for the selected strict tail

Stage 36 fix 1 compiler-promotes the erase-closed selected strict-tail family and the
coordinatewise erase pairing.  The remaining gap is the singleton boundary: bounding
each coordinate marginal by `p * closureMass` is too coarse because the closure contains
the singleton `{i}` in addition to the non-singleton strict accepted family.

This module replaces the coordinatewise bound by a prefix-erasure argument on the
ordered strict tail.  For the `r`-th tail coordinate, repeatedly erase any earlier tail
flip.  Each erase step gives one factor `1-p`; consequently

`(1-p)^r * flipMass(r) <= firstFlipMass(r)`.

The first-flip families are disjoint and telescope to exactly the non-singleton closure
mass.  Combining this with the Stage-35 coefficient envelope

`g_r <= g_i * (1-p)^r`

proves the Stage-34 selected bad-mass certificate at the standard mutation rate and
therefore closes the sharp `1/(e n)` one-step multiplicative-drift theorem.
-/

/-! ## Generic finite mask-family erase pairing -/

/-- Restrict a finite mutation-mask family to masks that flip coordinate `j`. -/
noncomputable def stage37MaskFamilyWithFlipAt {n : ℕ}
    (D : Finset (MutationMask n)) (j : Fin n) : Finset (MutationMask n) :=
  D.filter (fun mask => j ∈ mask)

/-- Restrict a finite mutation-mask family to masks that do not flip coordinate `j`. -/
noncomputable def stage37MaskFamilyWithoutFlipAt {n : ℕ}
    (D : Finset (MutationMask n)) (j : Fin n) : Finset (MutationMask n) :=
  D.filter (fun mask => j ∉ mask)

/-- Mutation mass of a finite mask family. -/
noncomputable def stage37MaskFamilyMass {n : ℕ}
    (p : ℝ) (D : Finset (MutationMask n)) : ℝ :=
  ∑ mask ∈ D, mutationMaskWeight p mask

@[simp] theorem mem_stage37MaskFamilyWithFlipAt {n : ℕ}
    (D : Finset (MutationMask n)) (j : Fin n) (mask : MutationMask n) :
    mask ∈ stage37MaskFamilyWithFlipAt D j ↔ mask ∈ D ∧ j ∈ mask := by
  classical
  simp [stage37MaskFamilyWithFlipAt]

@[simp] theorem mem_stage37MaskFamilyWithoutFlipAt {n : ℕ}
    (D : Finset (MutationMask n)) (j : Fin n) (mask : MutationMask n) :
    mask ∈ stage37MaskFamilyWithoutFlipAt D j ↔ mask ∈ D ∧ j ∉ mask := by
  classical
  simp [stage37MaskFamilyWithoutFlipAt]

/-- Any finite family partitions by whether a fixed coordinate flips. -/
theorem stage37MaskFamilyMass_eq_with_add_without {n : ℕ}
    (p : ℝ) (D : Finset (MutationMask n)) (j : Fin n) :
    stage37MaskFamilyMass p D =
      stage37MaskFamilyMass p (stage37MaskFamilyWithFlipAt D j) +
        stage37MaskFamilyMass p (stage37MaskFamilyWithoutFlipAt D j) := by
  classical
  unfold stage37MaskFamilyMass stage37MaskFamilyWithFlipAt
    stage37MaskFamilyWithoutFlipAt
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hj : j ∈ mask <;> simp [hj]

/-- Mutation mass is nonnegative on every finite family for a genuine mutation
probability. -/
theorem stage37MaskFamilyMass_nonneg {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (D : Finset (MutationMask n)) :
    0 ≤ stage37MaskFamilyMass p D := by
  unfold stage37MaskFamilyMass
  apply Finset.sum_nonneg
  intro mask hmask
  exact mutationMaskWeight_nonneg hp0 hp1 mask

/-- Generic erase pairing.  If erasing `j` from every family member that flips `j`
stays in the family, then the usual Bernoulli balance compares the with-flip and
without-flip masses. -/
theorem stage37_one_sub_p_mul_withFlipMass_le_withoutFlipMass {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (MutationMask n)) (j : Fin n)
    (herase : ∀ mask ∈ D, j ∈ mask → mask.erase j ∈ D) :
    (1 - p) * stage37MaskFamilyMass p (stage37MaskFamilyWithFlipAt D j) ≤
      p * stage37MaskFamilyMass p (stage37MaskFamilyWithoutFlipAt D j) := by
  classical
  unfold stage37MaskFamilyMass
  rw [Finset.mul_sum, Finset.mul_sum]
  have herase_inj :
      Set.InjOn (fun mask : MutationMask n => mask.erase j)
        ↑(stage37MaskFamilyWithFlipAt D j) := by
    intro a ha b hb hab
    have hja : j ∈ a := ((mem_stage37MaskFamilyWithFlipAt D j a).mp ha).2
    have hjb : j ∈ b := ((mem_stage37MaskFamilyWithFlipAt D j b).mp hb).2
    have hab' : a.erase j = b.erase j := by simpa using hab
    calc
      a = insert j (a.erase j) := (Finset.insert_erase hja).symm
      _ = insert j (b.erase j) := by rw [hab']
      _ = b := Finset.insert_erase hjb
  have himage_subset :
      (stage37MaskFamilyWithFlipAt D j).image
          (fun mask : MutationMask n => mask.erase j) ⊆
        stage37MaskFamilyWithoutFlipAt D j := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨mask, hmask, rfl⟩
    have hdata := (mem_stage37MaskFamilyWithFlipAt D j mask).mp hmask
    exact (mem_stage37MaskFamilyWithoutFlipAt D j (mask.erase j)).2
      ⟨herase mask hdata.1 hdata.2, by simp⟩
  calc
    (∑ mask ∈ stage37MaskFamilyWithFlipAt D j,
        (1 - p) * mutationMaskWeight p mask) =
      ∑ mask ∈ stage37MaskFamilyWithFlipAt D j,
        p * mutationMaskWeight p (mask.erase j) := by
      apply Finset.sum_congr rfl
      intro mask hmask
      have hjmask : j ∈ mask :=
        ((mem_stage37MaskFamilyWithFlipAt D j mask).mp hmask).2
      exact mutationMaskWeight_erase_balance p mask j hjmask
    _ = ∑ z ∈ (stage37MaskFamilyWithFlipAt D j).image
          (fun mask : MutationMask n => mask.erase j),
        p * mutationMaskWeight p z := by
      symm
      exact Finset.sum_image herase_inj
    _ ≤ ∑ z ∈ stage37MaskFamilyWithoutFlipAt D j,
        p * mutationMaskWeight p z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      intro z hz hnotImage
      exact mul_nonneg hp0 (mutationMaskWeight_nonneg hp0 hp1 z)

/-- Downward closure at `j` contracts total family mass by one survival factor when the
`j`-flipping part is removed. -/
theorem stage37_one_sub_p_mul_familyMass_le_withoutFlipMass {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Finset (MutationMask n)) (j : Fin n)
    (herase : ∀ mask ∈ D, j ∈ mask → mask.erase j ∈ D) :
    (1 - p) * stage37MaskFamilyMass p D ≤
      stage37MaskFamilyMass p (stage37MaskFamilyWithoutFlipAt D j) := by
  have hpair := stage37_one_sub_p_mul_withFlipMass_le_withoutFlipMass
    hp0 hp1 D j herase
  have hpart := stage37MaskFamilyMass_eq_with_add_without p D j
  calc
    (1 - p) * stage37MaskFamilyMass p D =
        (1 - p) * stage37MaskFamilyMass p (stage37MaskFamilyWithFlipAt D j) +
          (1 - p) * stage37MaskFamilyMass p
            (stage37MaskFamilyWithoutFlipAt D j) := by
      rw [hpart]
      ring
    _ ≤ p * stage37MaskFamilyMass p (stage37MaskFamilyWithoutFlipAt D j) +
          (1 - p) * stage37MaskFamilyMass p
            (stage37MaskFamilyWithoutFlipAt D j) := by
      exact add_le_add_left hpair _
    _ = stage37MaskFamilyMass p (stage37MaskFamilyWithoutFlipAt D j) := by
      ring

/-! ## Ordered strict-tail prefix families -/

/-- The actual coordinate at ordered strict-tail rank `r`. -/
noncomputable def wittStandardStrictTailCoordinate {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) : Fin n :=
  (wittStandardStrictTailOrder w x i r).1

/-- Every ordered strict-tail coordinate lies in the state-dependent tail. -/
theorem wittStandardStrictTailCoordinate_mem {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittStandardStrictTailCoordinate w x i r ∈
      wittStandardStrictTailIndices w x i := by
  exact (wittStandardStrictTailOrder w x i r).2

/-- Ordered strict-tail coordinates are injective in the rank. -/
theorem wittStandardStrictTailCoordinate_injective {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    Function.Injective (wittStandardStrictTailCoordinate w x i) := by
  intro r s hrs
  have hsub : wittStandardStrictTailOrder w x i r =
      wittStandardStrictTailOrder w x i s := by
    apply Subtype.ext
    exact hrs
  exact (wittStandardStrictTailOrder w x i).injective hsub

/-- Closure masks avoiding the first `m` ordered strict-tail coordinates. -/
noncomputable def wittStandardCaseC2AStrictClosureAvoidPrefixMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (m : ℕ) :
    Finset (MutationMask n) :=
  (wittStandardCaseC2AStrictClosureMasks w x i).filter (fun mask =>
    ∀ r : Fin (wittStandardStrictTailIndices w x i).card,
      r.val < m → wittStandardStrictTailCoordinate w x i r ∉ mask)

@[simp] theorem mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (m : ℕ)
    (mask : MutationMask n) :
    mask ∈ wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m ↔
      mask ∈ wittStandardCaseC2AStrictClosureMasks w x i ∧
        ∀ r : Fin (wittStandardStrictTailIndices w x i).card,
          r.val < m → wittStandardStrictTailCoordinate w x i r ∉ mask := by
  classical
  simp [wittStandardCaseC2AStrictClosureAvoidPrefixMasks]

/-- Prefix-avoiding closure mass. -/
noncomputable def wittStandardCaseC2AStrictClosureAvoidPrefixMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (m : ℕ) : ℝ :=
  stage37MaskFamilyMass p
    (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m)

/-- Prefix-avoiding closure masks that flip the target tail rank `r`. -/
noncomputable def wittStandardCaseC2AStrictTargetPrefixMasks {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) (m : ℕ) :
    Finset (MutationMask n) :=
  stage37MaskFamilyWithFlipAt
    (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m)
    (wittStandardStrictTailCoordinate w x i r)

/-- Mutation mass of the target-rank prefix family. -/
noncomputable def wittStandardCaseC2AStrictTargetPrefixMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) (m : ℕ) : ℝ :=
  stage37MaskFamilyMass p
    (wittStandardCaseC2AStrictTargetPrefixMasks w x i r m)

/-- First-tail-flip mass at rank `r`. -/
noncomputable def wittStandardCaseC2AStrictFirstFlipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) : ℝ :=
  wittStandardCaseC2AStrictTargetPrefixMass p w x i r r.val

/-- Avoiding an empty prefix imposes no additional restriction. -/
theorem wittStandardCaseC2AStrictClosureAvoidPrefixMasks_zero {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i 0 =
      wittStandardCaseC2AStrictClosureMasks w x i := by
  classical
  ext mask
  simp [wittStandardCaseC2AStrictClosureAvoidPrefixMasks]

/-- Hence target-prefix mass at prefix length zero is the ordinary closure flip mass. -/
theorem wittStandardCaseC2AStrictTargetPrefixMass_zero {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittStandardCaseC2AStrictTargetPrefixMass p w x i r 0 =
      wittStandardCaseC2AStrictClosureFlipAtMass p w x i
        (wittStandardStrictTailCoordinate w x i r) := by
  unfold wittStandardCaseC2AStrictTargetPrefixMass
    wittStandardCaseC2AStrictTargetPrefixMasks
    wittStandardCaseC2AStrictClosureFlipAtMass
    wittStandardCaseC2AStrictClosureWithFlipAt
  rw [wittStandardCaseC2AStrictClosureAvoidPrefixMasks_zero]
  rfl

/-- Removing the current rank from an already prefix-avoiding closure family advances
the avoided prefix by one. -/
theorem stage37_without_current_eq_avoidPrefix_succ {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    stage37MaskFamilyWithoutFlipAt
        (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i r.val)
        (wittStandardStrictTailCoordinate w x i r) =
      wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i (r.val + 1) := by
  classical
  ext mask
  constructor
  · intro hmask
    have hdata := (mem_stage37MaskFamilyWithoutFlipAt
      (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i r.val)
      (wittStandardStrictTailCoordinate w x i r) mask).mp hmask
    have hprefix := (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i r.val mask).mp hdata.1
    apply (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i (r.val + 1) mask).2
    refine ⟨hprefix.1, ?_⟩
    intro s hs
    by_cases hsr : s.val < r.val
    · exact hprefix.2 s hsr
    · have hval : s.val = r.val := by omega
      have hsrEq : s = r := Fin.ext hval
      simpa [hsrEq] using hdata.2
  · intro hmask
    have hprefix := (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i (r.val + 1) mask).mp hmask
    apply (mem_stage37MaskFamilyWithoutFlipAt
      (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i r.val)
      (wittStandardStrictTailCoordinate w x i r) mask).2
    refine ⟨?_, hprefix.2 r (by omega)⟩
    apply (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i r.val mask).2
    exact ⟨hprefix.1, fun s hs => hprefix.2 s (by omega)⟩

/-- Prefix mass partitions into the first-flip-at-current-rank mass and the next prefix
mass. -/
theorem wittStandardCaseC2AStrictClosureAvoidPrefixMass_eq_first_add_succ {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittStandardCaseC2AStrictClosureAvoidPrefixMass p w x i r.val =
      wittStandardCaseC2AStrictFirstFlipMass p w x i r +
        wittStandardCaseC2AStrictClosureAvoidPrefixMass p w x i (r.val + 1) := by
  unfold wittStandardCaseC2AStrictClosureAvoidPrefixMass
    wittStandardCaseC2AStrictFirstFlipMass
    wittStandardCaseC2AStrictTargetPrefixMass
    wittStandardCaseC2AStrictTargetPrefixMasks
  rw [stage37MaskFamilyMass_eq_with_add_without]
  rw [stage37_without_current_eq_avoidPrefix_succ]

/-- Erasing an earlier tail coordinate preserves a target-rank prefix family. -/
theorem erase_mem_wittStandardCaseC2AStrictTargetPrefixMasks {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card)
    (m : ℕ) (hm : m < r.val)
    (mask : MutationMask n)
    (hmask : mask ∈ wittStandardCaseC2AStrictTargetPrefixMasks w x i r m)
    (hjm : wittStandardStrictTailCoordinate w x i
      ⟨m, lt_trans hm r.isLt⟩ ∈ mask) :
    mask.erase (wittStandardStrictTailCoordinate w x i
      ⟨m, lt_trans hm r.isLt⟩) ∈
      wittStandardCaseC2AStrictTargetPrefixMasks w x i r m := by
  classical
  let s : Fin (wittStandardStrictTailIndices w x i).card :=
    ⟨m, lt_trans hm r.isLt⟩
  let jm : Fin n := wittStandardStrictTailCoordinate w x i s
  let jr : Fin n := wittStandardStrictTailCoordinate w x i r
  have hdata := (mem_stage37MaskFamilyWithFlipAt
    (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m) jr mask).mp
      (by simpa [wittStandardCaseC2AStrictTargetPrefixMasks, jm, jr, s] using hmask)
  have hprefix := (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
    w x i m mask).mp hdata.1
  have hsmem := wittStandardStrictTailCoordinate_mem w x i s
  have hsData := (mem_wittStandardStrictTailIndices w x i jm).mp (by simpa [jm] using hsmem)
  have hjbad : jm ∈ oneToZeroFlips x mask :=
    (mem_oneToZeroFlips x mask jm).2 ⟨by simpa [jm, s] using hjm, hsData.1⟩
  have heraseClosure := erase_oneToZero_mem_wittStandardCaseC2AStrictClosureMasks
    w hw x i mask jm hprefix.1 hjbad
  have hsr : s ≠ r := by
    intro h
    have hval := congrArg Fin.val h
    change m = r.val at hval
    omega
  have hjm_ne_jr : jm ≠ jr := by
    intro h
    exact hsr (wittStandardStrictTailCoordinate_injective w x i h)
  apply (mem_stage37MaskFamilyWithFlipAt
    (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m) jr
    (mask.erase jm)).2
  refine ⟨?_, Finset.mem_erase.mpr ⟨Ne.symm hjm_ne_jr, hdata.2⟩⟩
  apply (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
    w x i m (mask.erase jm)).2
  refine ⟨heraseClosure, ?_⟩
  intro t ht
  have hnot := hprefix.2 t ht
  exact fun hmem => hnot (Finset.mem_erase.mp hmem).2

/-- Inside a target-rank family, removing the next earlier coordinate advances the
avoided prefix by one. -/
theorem stage37_targetPrefix_without_next_eq_succ {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card)
    (m : ℕ) (hm : m < r.val) :
    stage37MaskFamilyWithoutFlipAt
        (wittStandardCaseC2AStrictTargetPrefixMasks w x i r m)
        (wittStandardStrictTailCoordinate w x i ⟨m, lt_trans hm r.isLt⟩) =
      wittStandardCaseC2AStrictTargetPrefixMasks w x i r (m + 1) := by
  classical
  let s : Fin (wittStandardStrictTailIndices w x i).card :=
    ⟨m, lt_trans hm r.isLt⟩
  let jm : Fin n := wittStandardStrictTailCoordinate w x i s
  let jr : Fin n := wittStandardStrictTailCoordinate w x i r
  ext mask
  constructor
  · intro hmask
    have hdata := (mem_stage37MaskFamilyWithoutFlipAt
      (wittStandardCaseC2AStrictTargetPrefixMasks w x i r m) jm mask).mp
      (by simpa [jm, s] using hmask)
    have htarget := (mem_stage37MaskFamilyWithFlipAt
      (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m) jr mask).mp
      (by simpa [wittStandardCaseC2AStrictTargetPrefixMasks, jr] using hdata.1)
    have hprefix := (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i m mask).mp htarget.1
    apply (mem_stage37MaskFamilyWithFlipAt
      (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i (m + 1)) jr mask).2
    refine ⟨?_, htarget.2⟩
    apply (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i (m + 1) mask).2
    refine ⟨hprefix.1, ?_⟩
    intro t ht
    by_cases htm : t.val < m
    · exact hprefix.2 t htm
    · have htval : t.val = m := by omega
      have htEq : t = s := Fin.ext htval
      simpa [htEq, jm] using hdata.2
  · intro hmask
    have htarget := (mem_stage37MaskFamilyWithFlipAt
      (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i (m + 1)) jr mask).mp
      (by simpa [wittStandardCaseC2AStrictTargetPrefixMasks, jr] using hmask)
    have hprefix := (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i (m + 1) mask).mp htarget.1
    apply (mem_stage37MaskFamilyWithoutFlipAt
      (wittStandardCaseC2AStrictTargetPrefixMasks w x i r m) jm mask).2
    refine ⟨?_, ?_⟩
    · apply (mem_stage37MaskFamilyWithFlipAt
        (wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i m) jr mask).2
      refine ⟨?_, htarget.2⟩
      apply (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
        w x i m mask).2
      exact ⟨hprefix.1, fun t ht => hprefix.2 t (by omega)⟩
    · exact hprefix.2 s (by simp [s])

/-- One survival factor contracts target-rank mass when one more earlier coordinate is
forbidden. -/
theorem one_sub_p_mul_wittStandardCaseC2AStrictTargetPrefixMass_le_succ {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card)
    (m : ℕ) (hm : m < r.val) :
    (1 - p) * wittStandardCaseC2AStrictTargetPrefixMass p w x i r m ≤
      wittStandardCaseC2AStrictTargetPrefixMass p w x i r (m + 1) := by
  let s : Fin (wittStandardStrictTailIndices w x i).card :=
    ⟨m, lt_trans hm r.isLt⟩
  let jm : Fin n := wittStandardStrictTailCoordinate w x i s
  have hcontract := stage37_one_sub_p_mul_familyMass_le_withoutFlipMass
    hp0 hp1 (wittStandardCaseC2AStrictTargetPrefixMasks w x i r m) jm
    (fun mask hmask hjm =>
      erase_mem_wittStandardCaseC2AStrictTargetPrefixMasks
        w hw x i r m hm mask hmask (by simpa [jm, s] using hjm))
  unfold wittStandardCaseC2AStrictTargetPrefixMass at hcontract ⊢
  rw [stage37_targetPrefix_without_next_eq_succ w x i r m hm] at hcontract
  exact hcontract

/-- Repeated prefix erasure: the closure marginal at rank `r`, multiplied by the `r`
survival factors, is at most the mass whose first flipped tail coordinate is `r`. -/
theorem standardSurvival_pow_mul_wittStandardCaseC2AStrictClosureFlipAtMass_le_firstFlipMass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    (1 - p) ^ r.val *
        wittStandardCaseC2AStrictClosureFlipAtMass p w x i
          (wittStandardStrictTailCoordinate w x i r) ≤
      wittStandardCaseC2AStrictFirstFlipMass p w x i r := by
  have hsurv : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hind : ∀ m : ℕ, m ≤ r.val →
      (1 - p) ^ m *
          wittStandardCaseC2AStrictTargetPrefixMass p w x i r 0 ≤
        wittStandardCaseC2AStrictTargetPrefixMass p w x i r m := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp
    | succ m ih =>
        intro hm
        have hmle : m ≤ r.val := Nat.le_trans (Nat.le_succ m) hm
        have hmlt : m < r.val := by omega
        have hprev := ih hmle
        have hmul := mul_le_mul_of_nonneg_left hprev hsurv
        have hstep :=
          one_sub_p_mul_wittStandardCaseC2AStrictTargetPrefixMass_le_succ
            hp0 hp1 w hw x i r m hmlt
        calc
          (1 - p) ^ (m + 1) *
              wittStandardCaseC2AStrictTargetPrefixMass p w x i r 0 =
            (1 - p) * ((1 - p) ^ m *
              wittStandardCaseC2AStrictTargetPrefixMass p w x i r 0) := by
              rw [pow_succ]
              ring
          _ ≤ (1 - p) *
              wittStandardCaseC2AStrictTargetPrefixMass p w x i r m := hmul
          _ ≤ wittStandardCaseC2AStrictTargetPrefixMass p w x i r (m + 1) := hstep
  have h := hind r.val le_rfl
  rw [wittStandardCaseC2AStrictTargetPrefixMass_zero] at h
  exact h

/-! ## First-flip masses telescope to the non-singleton closure -/

/-- Elementary telescoping identity for a real sequence indexed by `Fin k`. -/
private theorem stage37_fin_sum_consecutive_sub (A : ℕ → ℝ) (k : ℕ) :
    (∑ r : Fin k, (A r.val - A (r.val + 1))) = A 0 - A k := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_succ]
      have htail :
          (∑ r : Fin k, (A (r.val + 1) - A (r.val + 2))) =
            A 1 - A (k + 1) := by
        simpa [Nat.add_assoc] using (ih (fun m => A (m + 1)))
      change (A 0 - A 1) +
          (∑ r : Fin k, (A (r.val + 1) - A (r.val + 2))) =
        A 0 - A (k + 1)
      rw [htail]
      ring

/-- First-flip mass is the drop between two consecutive prefix-avoidance masses. -/
theorem wittStandardCaseC2AStrictFirstFlipMass_eq_prefixMass_sub_succ {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittStandardCaseC2AStrictFirstFlipMass p w x i r =
      wittStandardCaseC2AStrictClosureAvoidPrefixMass p w x i r.val -
        wittStandardCaseC2AStrictClosureAvoidPrefixMass p w x i (r.val + 1) := by
  have hpart := wittStandardCaseC2AStrictClosureAvoidPrefixMass_eq_first_add_succ
    p w x i r
  linarith

/-- Avoiding the whole strict tail leaves exactly the singleton boundary. -/
theorem wittStandardCaseC2AStrictClosureAvoidPrefixMasks_card_eq_singleton {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i
        (wittStandardStrictTailIndices w x i).card =
      {({i} : MutationMask n)} := by
  classical
  let T : Finset (Fin n) := wittStandardStrictTailIndices w x i
  let e := wittStandardStrictTailOrder w x i
  ext mask
  constructor
  · intro hmask
    have hprefix := (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks
      w x i T.card mask).mp (by simpa [T] using hmask)
    by_cases hsingle : mask = ({i} : MutationMask n)
    · simp [hsingle]
    · exfalso
      have heraseMem : mask ∈
            (wittStandardCaseC2AStrictClosureMasks w x i).erase
              ({i} : MutationMask n) := Finset.mem_erase.mpr ⟨hsingle, hprefix.1⟩
      have hstrict : mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i := by
        rw [wittStandardCaseC2AStrictAcceptedMasks_eq_closure_erase_singleton]
        exact heraseMem
      have hstrictData :=
        (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hstrict
      have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
        w x i mask).mp hstrictData.1
      have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
      have hbad := oneToZeroFlips_nonempty_of_caseC2At_of_ne_singleton
        x mask i hAdata.1.1 hbase.2
      rcases hbad with ⟨j, hjone⟩
      have hjT := oneToZeroFlips_subset_wittStandardStrictTailIndices
        w x i mask hstrict hjone
      let r : Fin T.card := e.symm ⟨j, by simpa [T] using hjT⟩
      have hrlt : r.val < T.card := r.isLt
      have hcoord : wittStandardStrictTailCoordinate w x i r = j := by
        have happly := e.apply_symm_apply ⟨j, by simpa [T] using hjT⟩
        have hval := congrArg Subtype.val happly
        simp [wittStandardStrictTailCoordinate, e, r] at hval ⊢
      have hjmask := ((mem_oneToZeroFlips x mask j).mp hjone).1
      have hnot : wittStandardStrictTailCoordinate w x i r ∉ mask :=
        hprefix.2 r hrlt
      apply hnot
      rw [hcoord]
      exact hjmask
  · intro hmask
    have hm : mask = ({i} : MutationMask n) := by simpa using hmask
    subst mask
    apply (mem_wittStandardCaseC2AStrictClosureAvoidPrefixMasks w x i
      (wittStandardStrictTailIndices w x i).card ({i} : MutationMask n)).2
    refine ⟨singleton_mem_wittStandardCaseC2AStrictClosureMasks w hw x i hi, ?_⟩
    intro r hr
    have hrData := (mem_wittStandardStrictTailIndices w x i
      (wittStandardStrictTailCoordinate w x i r)).mp
      (wittStandardStrictTailCoordinate_mem w x i r)
    have hne : wittStandardStrictTailCoordinate w x i r ≠ i := by
      intro h
      have hlt := hrData.2
      rw [h] at hlt
      exact (lt_irrefl _ hlt)
    simp [hne]

/-- Full-prefix mass is exactly the singleton mutation mass. -/
theorem wittStandardCaseC2AStrictClosureAvoidPrefixMass_card_eq_singletonRate {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictClosureAvoidPrefixMass p w x i
        (wittStandardStrictTailIndices w x i).card =
      linearSingletonRate n p := by
  unfold wittStandardCaseC2AStrictClosureAvoidPrefixMass stage37MaskFamilyMass
  rw [wittStandardCaseC2AStrictClosureAvoidPrefixMasks_card_eq_singleton
    w hw x i hi]
  simp [linearSingletonRate, mutationMaskWeight_singleton]

/-- The first-flip masses partition exactly the Stage-34 selected non-singleton strict
accepted mass. -/
theorem sum_wittStandardCaseC2AStrictFirstFlipMass_eq_strictAcceptedMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    (∑ r : Fin (wittStandardStrictTailIndices w x i).card,
      wittStandardCaseC2AStrictFirstFlipMass p w x i r) =
      wittStandardCaseC2AStrictAcceptedMass p w x i := by
  let A : ℕ → ℝ := fun m =>
    wittStandardCaseC2AStrictClosureAvoidPrefixMass p w x i m
  have htel := stage37_fin_sum_consecutive_sub A
    (wittStandardStrictTailIndices w x i).card
  have hfirst :
      (∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittStandardCaseC2AStrictFirstFlipMass p w x i r) =
      A 0 - A (wittStandardStrictTailIndices w x i).card := by
    rw [← htel]
    apply Finset.sum_congr rfl
    intro r hr
    rw [wittStandardCaseC2AStrictFirstFlipMass_eq_prefixMass_sub_succ]
  rw [hfirst]
  have hzero : A 0 = wittStandardCaseC2AStrictClosureMass p w x i := by
    dsimp [A, wittStandardCaseC2AStrictClosureAvoidPrefixMass,
      wittStandardCaseC2AStrictClosureMass, stage37MaskFamilyMass]
    rw [wittStandardCaseC2AStrictClosureAvoidPrefixMasks_zero]
  have hcard : A (wittStandardStrictTailIndices w x i).card =
      linearSingletonRate n p := by
    exact wittStandardCaseC2AStrictClosureAvoidPrefixMass_card_eq_singletonRate
      p w hw x i hi
  rw [hzero, hcard]
  have hclosure := wittStandardCaseC2AStrictClosureMass_eq_singleton_add_strictMass
    p w hw x i hi
  linarith

/-! ## Selected bad-mass closure -/

/-- Reindex the selected strict bad mass by ordered strict-tail rank. -/
theorem wittStandardCaseC2AStrictBadMass_eq_sum_ordered_closureFlipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (hi : x i = false) :
    wittStandardCaseC2AStrictBadMass p w x i =
      ∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittStandardPotentialWeight w
            (wittStandardStrictTailCoordinate w x i r) *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (wittStandardStrictTailCoordinate w x i r) := by
  rw [wittStandardCaseC2AStrictBadMass_eq_sum_tail_closureFlipMass
    p w x i hi]
  let T : Finset (Fin n) := wittStandardStrictTailIndices w x i
  have himage :
      Finset.image (fun r : Fin T.card => T.orderEmbOfFin rfl r) Finset.univ = T :=
    T.image_orderEmbOfFin_univ rfl
  calc
    (∑ j ∈ wittStandardStrictTailIndices w x i,
      wittStandardPotentialWeight w j *
        wittStandardCaseC2AStrictClosureFlipAtMass p w x i j) =
      ∑ j ∈ Finset.image (fun r : Fin T.card => T.orderEmbOfFin rfl r) Finset.univ,
        wittStandardPotentialWeight w j *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i j := by
        rw [himage]
    _ = ∑ r : Fin T.card,
        wittStandardPotentialWeight w (T.orderEmbOfFin rfl r) *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (T.orderEmbOfFin rfl r) := by
      rw [Finset.sum_image (by
        intro a _ b _ hab
        exact (T.orderEmbOfFin rfl).injective hab)]
    _ = ∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittStandardPotentialWeight w
            (wittStandardStrictTailCoordinate w x i r) *
          wittStandardCaseC2AStrictClosureFlipAtMass p w x i
            (wittStandardStrictTailCoordinate w x i r) := by
      rfl

/-- The aggregate prefix-erasure estimate closes the selected strict-tail bad-mass
bound at the standard mutation rate. -/
theorem wittStandardCaseC2AStrictBadMass_le_good_mul_strictAcceptedMass {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardCaseC2AStrictBadMass (standardMutationRate n) w x i ≤
      wittStandardPotentialWeight w i *
        wittStandardCaseC2AStrictAcceptedMass
          (standardMutationRate n) w x i := by
  have hp := standardMutationRate_mem_unitInterval_linear hn
  rw [wittStandardCaseC2AStrictBadMass_eq_sum_ordered_closureFlipMass
    (standardMutationRate n) w x i hi]
  calc
    (∑ r : Fin (wittStandardStrictTailIndices w x i).card,
      wittStandardPotentialWeight w
          (wittStandardStrictTailCoordinate w x i r) *
        wittStandardCaseC2AStrictClosureFlipAtMass (standardMutationRate n) w x i
          (wittStandardStrictTailCoordinate w x i r)) ≤
      ∑ r : Fin (wittStandardStrictTailIndices w x i).card,
        wittStandardPotentialWeight w i *
          wittStandardCaseC2AStrictFirstFlipMass
            (standardMutationRate n) w x i r := by
      apply Finset.sum_le_sum
      intro r hr
      have hweight := wittStandardStrictTail_ordered_weight_le
        hn w hmono x i r
      have hmassNonneg :
          0 ≤ wittStandardCaseC2AStrictClosureFlipAtMass
            (standardMutationRate n) w x i
              (wittStandardStrictTailCoordinate w x i r) := by
        unfold wittStandardCaseC2AStrictClosureFlipAtMass
        apply Finset.sum_nonneg
        intro mask hmask
        exact mutationMaskWeight_nonneg hp.1 hp.2 mask
      have hprefix :=
        standardSurvival_pow_mul_wittStandardCaseC2AStrictClosureFlipAtMass_le_firstFlipMass
          hp.1 hp.2 w hw x i r
      have hgoodNonneg := (wittStandardPotentialWeight_pos w i).le
      calc
        wittStandardPotentialWeight w (wittStandardStrictTailCoordinate w x i r) *
            wittStandardCaseC2AStrictClosureFlipAtMass
              (standardMutationRate n) w x i
                (wittStandardStrictTailCoordinate w x i r) ≤
          (wittStandardPotentialWeight w i *
              (1 - standardMutationRate n) ^ r.val) *
            wittStandardCaseC2AStrictClosureFlipAtMass
              (standardMutationRate n) w x i
                (wittStandardStrictTailCoordinate w x i r) :=
          mul_le_mul_of_nonneg_right hweight hmassNonneg
        _ = wittStandardPotentialWeight w i *
            ((1 - standardMutationRate n) ^ r.val *
              wittStandardCaseC2AStrictClosureFlipAtMass
                (standardMutationRate n) w x i
                  (wittStandardStrictTailCoordinate w x i r)) := by ring
        _ ≤ wittStandardPotentialWeight w i *
            wittStandardCaseC2AStrictFirstFlipMass
              (standardMutationRate n) w x i r :=
          mul_le_mul_of_nonneg_left hprefix hgoodNonneg
    _ = wittStandardPotentialWeight w i *
        (∑ r : Fin (wittStandardStrictTailIndices w x i).card,
          wittStandardCaseC2AStrictFirstFlipMass
            (standardMutationRate n) w x i r) := by
      rw [Finset.mul_sum]
    _ = wittStandardPotentialWeight w i *
        wittStandardCaseC2AStrictAcceptedMass
          (standardMutationRate n) w x i := by
      rw [sum_wittStandardCaseC2AStrictFirstFlipMass_eq_strictAcceptedMass
        (standardMutationRate n) w hw x i hi]

/-- The explicit Stage-34 selected bad-mass certificate now holds unconditionally for
positive nonincreasing linear weights. -/
theorem wittStandard_hasStrictC2ABadMassBound {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasWittStandardStrictC2ABadMassBound w := by
  intro x i hi
  exact wittStandardCaseC2AStrictBadMass_le_good_mul_strictAcceptedMass
    hn w hw hmono x i hi

/-- Sharp standard-rate one-step multiplicative drift for every positive nonincreasing
linear objective, with no remaining C2/C3 certificate assumptions. -/
theorem wittStandard_hasMultiplicativeDriftLowerBound_sharp {n : ℕ}
    (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (standardMutationRate n) (linearFitness w))
      (wittStandardLinearPotential w)
      (wittStandardLinearDriftRate n) := by
  apply wittStandard_hasMultiplicativeDriftLowerBound_of_strictC2ABadMassBound
    hn w hw hmono
  exact wittStandard_hasStrictC2ABadMassBound (by omega) w hw hmono

end ECRuntime
