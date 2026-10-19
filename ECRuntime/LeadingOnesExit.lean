import ECRuntime.LeadingOnes
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 27 fix 2: exact LeadingOnes level-exit mutation masks

For a state whose LeadingOnes value is `i < n`, an offspring leaves level `i`
exactly when mutation flips coordinate `i` and leaves every earlier coordinate
unchanged.  Coordinates after `i` are unrestricted.  This file formalizes that
deterministic characterization and a canonical suffix-mask parameterization.

The parameterization also gives the exact total independent-bit mutation weight
`p * (1-p)^i`: one prescribed flip, `i` prescribed non-flips, and an arbitrary
suffix whose weights sum to one.
-/

/-- Coordinate condition for a mutation mask to leave LeadingOnes level `i`. -/
def leadingOnesExitMaskEvent {n : ℕ} (i : Fin n) (mask : MutationMask n) : Prop :=
  i ∈ mask ∧ ∀ j : Fin n, j.val < i.val → j ∉ mask

/-- If every bit through coordinate `i` is one, then the LeadingOnes value exceeds `i`. -/
theorem leadingOnes_gt_of_prefix_true :
    ∀ {n : ℕ} (x : BitString n) (i : Fin n),
      (∀ j : Fin n, j.val ≤ i.val → x j = true) →
      i.val < leadingOnes x := by
  intro n
  induction n with
  | zero =>
      intro x i
      exact Fin.elim0 i
  | succ n ih =>
      intro x i hprefix
      have h0 : x 0 = true := hprefix 0 (by simp)
      rw [leadingOnes_succ, if_pos h0]
      by_cases hi0 : i.val = 0
      · omega
      · have hiPos : 0 < i.val := by omega
        have hiTailLt : i.val - 1 < n := by
          have hiLt := i.isLt
          omega
        let j : Fin n := ⟨i.val - 1, hiTailLt⟩
        have htail :
            ∀ k : Fin n, k.val ≤ j.val → bitStringTail x k = true := by
          intro k hk
          apply hprefix k.succ
          change k.val + 1 ≤ i.val
          dsimp [j] at hk
          omega
        have hih : j.val < leadingOnes (bitStringTail x) :=
          ih (bitStringTail x) j htail
        dsimp [j] at hih
        omega

/-- At an exact nonterminal LeadingOnes level, the first uncertified bit is zero. -/
theorem bit_eq_false_of_leadingOnes_eq
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hlevel : leadingOnes x = i.val) :
    x i = false := by
  by_cases hxi : x i = false
  · exact hxi
  · have hxiTrue : x i = true := Bool.eq_true_of_not_eq_false hxi
    exfalso
    have hall : ∀ j : Fin n, j.val ≤ i.val → x j = true := by
      intro j hj
      rcases lt_or_eq_of_le hj with hlt | heq
      · apply bit_eq_true_of_lt_leadingOnes x j
        rw [hlevel]
        exact hlt
      · have hji : j = i := Fin.ext heq
        simpa [hji] using hxiTrue
    have hgt := leadingOnes_gt_of_prefix_true x i hall
    rw [hlevel] at hgt
    omega

/-- Exact deterministic characterization of a one-step LeadingOnes level exit. -/
theorem leadingOnes_mutation_exits_iff
    {n : ℕ} (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hlevel : leadingOnes x = i.val) :
    i.val < leadingOnes (mutateWithMask x mask) ↔
      leadingOnesExitMaskEvent i mask := by
  constructor
  · intro hgt
    have hcritFalse := bit_eq_false_of_leadingOnes_eq x i hlevel
    have hcritTrue : mutateWithMask x mask i = true :=
      bit_eq_true_of_lt_leadingOnes (mutateWithMask x mask) i hgt
    have hiMem : i ∈ mask := by
      by_contra hiNot
      simp [mutateWithMask, hiNot, hcritFalse] at hcritTrue
    refine ⟨hiMem, ?_⟩
    intro j hjlt hjMem
    have hxj : x j = true := by
      apply bit_eq_true_of_lt_leadingOnes x j
      rw [hlevel]
      exact hjlt
    have hmutj : mutateWithMask x mask j = true := by
      apply bit_eq_true_of_lt_leadingOnes (mutateWithMask x mask) j
      exact lt_trans hjlt hgt
    simp [mutateWithMask, hjMem, hxj] at hmutj
  · rintro ⟨hiMem, hprefixNoFlip⟩
    apply leadingOnes_gt_of_prefix_true (mutateWithMask x mask) i
    intro j hjle
    rcases lt_or_eq_of_le hjle with hjlt | hjeq
    · have hxj : x j = true := by
        apply bit_eq_true_of_lt_leadingOnes x j
        rw [hlevel]
        exact hjlt
      have hjNot := hprefixNoFlip j hjlt
      simp [mutateWithMask, hjNot, hxj]
    · have hji : j = i := Fin.ext hjeq
      subst j
      have hcritFalse := bit_eq_false_of_leadingOnes_eq x i hlevel
      simp [mutateWithMask, hiMem, hcritFalse]

/-- Embed suffix coordinates strictly after a fixed LeadingOnes level. -/
def leadingOnesSuffixEmbedding {n : ℕ} (i : Fin n) :
    Fin (n - (i.val + 1)) ↪ Fin n where
  toFun k :=
    ⟨i.val + 1 + k.val, by
      have hi : i.val + 1 ≤ n := by omega
      have hk := k.isLt
      omega⟩
  inj' := by
    intro a b hab
    have hval : i.val + 1 + a.val = i.val + 1 + b.val :=
      congrArg Fin.val hab
    apply Fin.ext
    omega

/-- Canonical mask: flip the level bit and an arbitrary suffix, but no prefix bit. -/
def leadingOnesExitMask {n : ℕ} (i : Fin n)
    (suffix : MutationMask (n - (i.val + 1))) : MutationMask n :=
  insert i (suffix.map (leadingOnesSuffixEmbedding i))

@[simp] theorem leadingOnesExitMask_level_mem
    {n : ℕ} (i : Fin n) (suffix : MutationMask (n - (i.val + 1))) :
    i ∈ leadingOnesExitMask i suffix := by
  simp [leadingOnesExitMask]

/-- No coordinate below the current LeadingOnes level occurs in a canonical exit mask. -/
theorem leadingOnesExitMask_prefix_not_mem
    {n : ℕ} (i j : Fin n) (suffix : MutationMask (n - (i.val + 1)))
    (hj : j.val < i.val) :
    j ∉ leadingOnesExitMask i suffix := by
  intro hmem
  simp only [leadingOnesExitMask, Finset.mem_insert, Finset.mem_map] at hmem
  rcases hmem with hji | ⟨k, hk, hkj⟩
  · have hval := congrArg Fin.val hji
    omega
  · have hval := congrArg Fin.val hkj
    change i.val + 1 + k.val = j.val at hval
    omega

/-- Every canonical suffix mask satisfies the exact level-exit coordinate condition. -/
theorem leadingOnesExitMask_event
    {n : ℕ} (i : Fin n) (suffix : MutationMask (n - (i.val + 1))) :
    leadingOnesExitMaskEvent i (leadingOnesExitMask i suffix) := by
  refine ⟨leadingOnesExitMask_level_mem i suffix, ?_⟩
  intro j hj
  exact leadingOnesExitMask_prefix_not_mem i j suffix hj

/-- Extract the unrestricted suffix part of an arbitrary full mutation mask. -/
def leadingOnesExitSuffixOfMask {n : ℕ} (i : Fin n) (mask : MutationMask n) :
    MutationMask (n - (i.val + 1)) :=
  Finset.univ.filter (fun k => leadingOnesSuffixEmbedding i k ∈ mask)

@[simp] theorem mem_leadingOnesExitSuffixOfMask
    {n : ℕ} (i : Fin n) (mask : MutationMask n)
    (k : Fin (n - (i.val + 1))) :
    k ∈ leadingOnesExitSuffixOfMask i mask ↔
      leadingOnesSuffixEmbedding i k ∈ mask := by
  simp [leadingOnesExitSuffixOfMask]

/-- A mask satisfying the exit-coordinate condition is reconstructed from its suffix. -/
theorem leadingOnesExitMask_suffixOfMask_eq_of_event
    {n : ℕ} (i : Fin n) (mask : MutationMask n)
    (hEvent : leadingOnesExitMaskEvent i mask) :
    leadingOnesExitMask i (leadingOnesExitSuffixOfMask i mask) = mask := by
  ext j
  constructor
  · intro hj
    simp only [leadingOnesExitMask, Finset.mem_insert, Finset.mem_map] at hj
    rcases hj with hji | ⟨k, hk, hkj⟩
    · subst j
      exact hEvent.1
    · have hkMask : leadingOnesSuffixEmbedding i k ∈ mask :=
        (mem_leadingOnesExitSuffixOfMask i mask k).1 hk
      rw [hkj] at hkMask
      exact hkMask
  · intro hjMask
    by_cases hji : j = i
    · subst j
      exact leadingOnesExitMask_level_mem i (leadingOnesExitSuffixOfMask i mask)
    · have hnotlt : ¬ j.val < i.val := by
        intro hjlt
        exact (hEvent.2 j hjlt) hjMask
      have hneval : j.val ≠ i.val := by
        intro hval
        apply hji
        exact Fin.ext hval
      have hgt : i.val < j.val := by omega
      let kVal : ℕ := j.val - (i.val + 1)
      have hkLt : kVal < n - (i.val + 1) := by
        dsimp [kVal]
        have hjN := j.isLt
        omega
      let k : Fin (n - (i.val + 1)) := ⟨kVal, hkLt⟩
      have hkEq : leadingOnesSuffixEmbedding i k = j := by
        apply Fin.ext
        dsimp [leadingOnesSuffixEmbedding, k, kVal]
        omega
      have hkSuffix : k ∈ leadingOnesExitSuffixOfMask i mask := by
        rw [mem_leadingOnesExitSuffixOfMask]
        rw [hkEq]
        exact hjMask
      rw [leadingOnesExitMask]
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_map]
      exact ⟨k, hkSuffix, hkEq⟩

/-- Extracting the suffix of a canonical exit mask recovers the original suffix. -/
theorem leadingOnesExitSuffixOfMask_exitMask
    {n : ℕ} (i : Fin n) (suffix : MutationMask (n - (i.val + 1))) :
    leadingOnesExitSuffixOfMask i (leadingOnesExitMask i suffix) = suffix := by
  ext k
  have hne : leadingOnesSuffixEmbedding i k ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    change i.val + 1 + k.val = i.val at hval
    omega
  simp [leadingOnesExitSuffixOfMask, leadingOnesExitMask, hne]

/-- The canonical suffix-mask parameterization has no duplicate full masks. -/
theorem leadingOnesExitMask_injective
    {n : ℕ} (i : Fin n) :
    Function.Injective (leadingOnesExitMask i) := by
  intro a b hab
  have h := congrArg (leadingOnesExitSuffixOfMask i) hab
  rw [leadingOnesExitSuffixOfMask_exitMask,
      leadingOnesExitSuffixOfMask_exitMask] at h
  exact h

/-- The coordinate event is represented by exactly one unrestricted suffix mask. -/
theorem leadingOnesExitMaskEvent_iff_existsUnique_suffix
    {n : ℕ} (i : Fin n) (mask : MutationMask n) :
    leadingOnesExitMaskEvent i mask ↔
      ∃! suffix : MutationMask (n - (i.val + 1)),
        leadingOnesExitMask i suffix = mask := by
  constructor
  · intro hEvent
    let suffix := leadingOnesExitSuffixOfMask i mask
    have hreconstruct : leadingOnesExitMask i suffix = mask := by
      exact leadingOnesExitMask_suffixOfMask_eq_of_event i mask hEvent
    refine ⟨suffix, hreconstruct, ?_⟩
    intro other hother
    apply leadingOnesExitMask_injective i
    calc
      leadingOnesExitMask i other = mask := hother
      _ = leadingOnesExitMask i suffix := hreconstruct.symm
  · rintro ⟨suffix, hmask, _⟩
    rw [← hmask]
    exact leadingOnesExitMask_event i suffix

/-- Every canonical exit mask leaves the current exact LeadingOnes level. -/
theorem leadingOnes_exitMask_causes_exit
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hlevel : leadingOnes x = i.val)
    (suffix : MutationMask (n - (i.val + 1))) :
    i.val < leadingOnes (mutateWithMask x (leadingOnesExitMask i suffix)) := by
  exact (leadingOnes_mutation_exits_iff x i (leadingOnesExitMask i suffix) hlevel).2
    (leadingOnesExitMask_event i suffix)

/-- A canonical exit mask has one prescribed level flip plus all chosen suffix flips. -/
theorem leadingOnesExitMask_card
    {n : ℕ} (i : Fin n) (suffix : MutationMask (n - (i.val + 1))) :
    (leadingOnesExitMask i suffix).card = suffix.card + 1 := by
  have hnot : i ∉ suffix.map (leadingOnesSuffixEmbedding i) := by
    intro hmem
    rw [Finset.mem_map] at hmem
    rcases hmem with ⟨k, hk, hki⟩
    have hval := congrArg Fin.val hki
    change i.val + 1 + k.val = i.val at hval
    omega
  simp [leadingOnesExitMask, hnot]

/-- Weight factorization for one prescribed flip, `i` prescribed non-flips, and a free suffix. -/
theorem mutationMaskWeight_leadingOnesExitMask
    {n : ℕ} (p : ℝ) (i : Fin n)
    (suffix : MutationMask (n - (i.val + 1))) :
    mutationMaskWeight p (leadingOnesExitMask i suffix) =
      p * (1 - p) ^ i.val * mutationMaskWeight p suffix := by
  have hsuffix : suffix.card ≤ n - (i.val + 1) := by
    simpa using (Finset.card_le_univ suffix)
  have hi : i.val + 1 ≤ n := by omega
  have hsub :
      n - (suffix.card + 1) =
        i.val + ((n - (i.val + 1)) - suffix.card) := by
    omega
  unfold mutationMaskWeight
  rw [leadingOnesExitMask_card, hsub, pow_succ, pow_add]
  ring

/--
Exact total mutation weight of the canonical family of LeadingOnes exit masks.
The suffix is unrestricted, so its independent-bit mutation weights sum to one.
-/
theorem leadingOnesExitMaskFamilyWeight_eq
    {n : ℕ} (p : ℝ) (i : Fin n) :
    (∑ suffix : MutationMask (n - (i.val + 1)),
      mutationMaskWeight p (leadingOnesExitMask i suffix)) =
      p * (1 - p) ^ i.val := by
  simp_rw [mutationMaskWeight_leadingOnesExitMask]
  rw [← Finset.mul_sum, mutationMaskWeight_sum]
  ring

end ECRuntime
