import ECRuntime.StaticUnaryUnbiasedShortRadiusPivot
import ECRuntime.StaticUnaryUnbiasedPairNormalization
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 94 proof candidate: radius-resolved accepted short-pivot loss

These approved statements refine Stage 93 by keeping acceptance
inside the short-pivot events while comparing their one-to-zero loss with
unconditional, radius-truncated **pair** marginals. No mutation law is
conditioned on acceptance or on a coordinate being flipped.

The pair identity uses the factorial moment truncated at `K < b` (written
`truncatedSecondFactorialRadiusMoment (b - 1)`), not the full second moment.
For `n >= 2`, its normalization is `n (n-1)`. The final drift envelope is
conservative and is NOT the sharp bounded-first-moment runtime theorem.

**PROOF VERIFICATION GATE:** The user approved the nine theorem statements.
The Stage 94 proof-1 strict focused compilation reported two tactic errors and
one unused-binder warning, addressed by proof-2. These edits have not been
recompiled in Lean; the module is not root-integrated, pinned, or promoted.
-/

/-- Original-law mass of short masks flipping two named coordinates.
No conditioning or renormalization is performed. -/
noncomputable def shortRadiusPairFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) (i j : Fin n) : ℝ := by
  classical
  exact ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
    if i ∈ mask ∧ j ∈ mask then law.weight mask else 0

/-- The Stage-93 accepted short-pivot remainder cannot contain masks of
radius zero or one; the improving singleton was erased explicitly. -/
theorem shortPivotRemainderEvent_card_ge_two {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (b : ℕ) (i : Fin n)
    (mask : MutationMask n)
    (hm : mask ∈ shortPivotRemainderEvent w x b i) :
    2 ≤ mask.card := by

  classical
  have hrest : mask ∈ shortAcceptedPivotEvent w x b i :=
    (Finset.mem_erase.mp hm).2
  have hnot : mask ≠ ({i} : MutationMask n) :=
    (Finset.mem_erase.mp hm).1
  have hpivot : mask ∈ acceptedLeftmostZeroEvent w x i := by
    unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
    exact (Finset.mem_filter.mp hrest).2
  have him : i ∈ mask :=
    acceptedLeftmostZeroEvent_supports_pivot w x i mask hpivot
  have hpos : 0 < mask.card := Finset.card_pos.mpr ⟨i, him⟩
  by_contra hlt
  have hone : mask.card = 1 := by omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
  have hij : i = j := by simpa [hj] using him
  subst j
  exact hnot hj

/-- Every Stage-93 short-pivot remainder retains its strict radius cutoff. -/
theorem shortPivotRemainderEvent_card_lt_cutoff {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (b : ℕ) (i : Fin n)
    (mask : MutationMask n)
    (hm : mask ∈ shortPivotRemainderEvent w x b i) :
    mask.card < b := by

  classical
  have hrest : mask ∈ shortAcceptedPivotEvent w x b i :=
    (Finset.mem_erase.mp hm).2
  unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
  have hshort : mask ∈ shortRadiusMaskEvent (n := n) b :=
    (Finset.mem_filter.mp hrest).1
  exact (Finset.mem_filter.mp hshort).2

/-- A one-to-zero loss in a short accepted pivot remainder forces a
*distinct* joint flip with that pivot, at the original radius `K < b`. -/
theorem shortPivotRemainderEvent_pair_membership {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (mask : MutationMask n)
    (hm : mask ∈ shortPivotRemainderEvent w x b i)
    (j : Fin n) (hj : j ∈ oneToZeroFlips x mask) :
    mask ∈ shortRadiusMaskEvent (n := n) b ∧
      i ∈ mask ∧ j ∈ mask ∧ i ≠ j := by

  classical
  have hrest : mask ∈ shortAcceptedPivotEvent w x b i :=
    (Finset.mem_erase.mp hm).2
  have hshort : mask ∈ shortRadiusMaskEvent (n := n) b := by
    unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
    exact (Finset.mem_filter.mp hrest).1
  have hpivot : mask ∈ acceptedLeftmostZeroEvent w x i := by
    unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
    exact (Finset.mem_filter.mp hrest).2
  have him : i ∈ mask :=
    acceptedLeftmostZeroEvent_supports_pivot w x i mask hpivot
  have hjm : j ∈ mask := ((mem_oneToZeroFlips x mask j).1 hj).1
  have hxi : x i = false :=
    acceptedLeftmostZeroEvent_pivot_is_zero w x i mask hpivot
  have hxj : x j = true := ((mem_oneToZeroFlips x mask j).1 hj).2
  have hij : i ≠ j := by
    intro heq
    subst j
    simp [hxi] at hxj
  exact ⟨hshort, him, hjm, hij⟩

/-! ## Radius-truncated pair symmetry and finite double counting

The auxiliary lemmas keep the *original* mask law.  We do not normalize
or condition it on the short-radius event. -/

/-- The factorial moment truncated at `b - 1` is exactly the corresponding
finite mask sum under the strict radius cutoff, also when `b = 0`. -/
private theorem truncatedSecondFactorialRadiusMoment_eq_short_mask_sum
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    law.truncatedSecondFactorialRadiusMoment (b - 1) =
      ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
        (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
  classical
  by_cases hb : b = 0
  · subst b
    have hzero : law.truncatedSecondFactorialRadiusMoment 0 = 0 := by
      unfold truncatedSecondFactorialRadiusMoment
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hkzero : k = 0
      · simp [hkzero]
      · have hknot : ¬ k ≤ 0 := by omega
        simp [hknot]
    simpa [shortRadiusMaskEvent] using hzero
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    unfold truncatedSecondFactorialRadiusMoment
    calc
      (∑ k ∈ Finset.range (n + 1),
        if k ≤ b - 1 then
          (k : ℝ) * ((k - 1 : ℕ) : ℝ) * law.radiusMass k else 0) =
          ∑ k ∈ Finset.range (n + 1),
            ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
              if mask.card < b then
                (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask
              else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkb : k < b
        · have hkle : k ≤ b - 1 := by omega
          simp only [if_pos hkle]
          unfold radiusMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mask hm
          have hcard : mask.card = k :=
            (Finset.mem_powersetCard.mp hm).2
          simp only [hcard, if_pos hkb]
        · have hknle : ¬ k ≤ b - 1 := by omega
          simp only [if_neg hknle]
          symm
          apply Finset.sum_eq_zero
          intro mask hm
          have hcard : mask.card = k :=
            (Finset.mem_powersetCard.mp hm).2
          simp only [hcard, if_neg hkb]
      _ = ∑ mask : MutationMask n,
            if mask.card < b then
              (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask
            else 0 := by
        simpa using (Finset.sum_powerset (Finset.univ : Finset (Fin n))
          (fun mask : MutationMask n =>
            if mask.card < b then
              (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask
            else 0)).symm
      _ = ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
            (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
        unfold shortRadiusMaskEvent
        rw [Finset.sum_filter]

/-- Truncated pair-flip mass is symmetric in the two named coordinates. -/
private theorem shortRadiusPairFlipMass_comm {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) (i j : Fin n) :
    law.shortRadiusPairFlipMass b i j = law.shortRadiusPairFlipMass b j i := by
  unfold shortRadiusPairFlipMass
  apply Finset.sum_congr rfl
  intro mask hm
  simp [and_comm]

/-- Truncated mass is invariant under swapping distinct second coordinates. -/
private theorem shortRadiusPairFlipMass_eq_of_same_first {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    law.shortRadiusPairFlipMass b i j = law.shortRadiusPairFlipMass b i k := by
  classical
  unfold shortRadiusPairFlipMass
  simp only [shortRadiusMaskEvent, Finset.sum_filter]
  let e : MutationMask n ≃ MutationMask n := swapMaskEquiv j k
  refine Fintype.sum_equiv e
    (fun mask : MutationMask n =>
      if mask.card < b then
        (if i ∈ mask ∧ j ∈ mask then law.weight mask else 0) else 0)
    (fun mask : MutationMask n =>
      if mask.card < b then
        (if i ∈ mask ∧ k ∈ mask then law.weight mask else 0) else 0) ?_
  intro mask
  have hcard : mask.card = (e mask).card := by simp [e]
  have hw : law.weight mask = law.weight (e mask) :=
    law.card_invariant hcard
  have hfix : (Equiv.swap j k) i = i :=
    Equiv.swap_apply_of_ne_of_ne hij hik
  have hiMem : i ∈ e mask ↔ i ∈ mask := by
    simp [e, swapMaskEquiv, hfix]
  have hkMem : k ∈ e mask ↔ j ∈ mask := by simp [e]
  by_cases hr : mask.card < b
  · have hre : (e mask).card < b := by simpa only [← hcard] using hr
    simp only [if_pos hr, if_pos hre]
    by_cases hi : i ∈ mask
    · have hie : i ∈ e mask := hiMem.mpr hi
      by_cases hj : j ∈ mask
      · have hke : k ∈ e mask := hkMem.mpr hj
        simp [hi, hj, hie, hke, hw]
      · have hkne : k ∉ e mask := by
          intro hk
          exact hj (hkMem.mp hk)
        simp [hi, hj, hie, hkne]
    · have hine : i ∉ e mask := by
        intro hie
        exact hi (hiMem.mp hie)
      simp [hi, hine]
  · have hre : ¬ (e mask).card < b := by
      intro he
      exact hr (by simpa only [hcard] using he)
    simp only [if_neg hr, if_neg hre]

/-- Every ordered pair of *distinct* coordinates has equal truncated mass. -/
private theorem shortRadiusPairFlipMass_eq_of_distinct {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ)
    (i j a c : Fin n) (hij : i ≠ j) (hac : a ≠ c) :
    law.shortRadiusPairFlipMass b i j = law.shortRadiusPairFlipMass b a c := by
  by_cases hja : j = a
  · subst a
    calc
      law.shortRadiusPairFlipMass b i j = law.shortRadiusPairFlipMass b j i :=
        law.shortRadiusPairFlipMass_comm b i j
      _ = law.shortRadiusPairFlipMass b j c :=
        law.shortRadiusPairFlipMass_eq_of_same_first b j i c (Ne.symm hij) hac
  · calc
      law.shortRadiusPairFlipMass b i j = law.shortRadiusPairFlipMass b j i :=
        law.shortRadiusPairFlipMass_comm b i j
      _ = law.shortRadiusPairFlipMass b j a :=
        law.shortRadiusPairFlipMass_eq_of_same_first b j i a (Ne.symm hij) hja
      _ = law.shortRadiusPairFlipMass b a j :=
        law.shortRadiusPairFlipMass_comm b j a
      _ = law.shortRadiusPairFlipMass b a c :=
        law.shortRadiusPairFlipMass_eq_of_same_first b a j c (Ne.symm hja) hac

/-- Ordered pair masses summed over all different named coordinates. -/
private noncomputable def orderedDistinctShortPairMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), law.shortRadiusPairFlipMass b i j

/-- For a fixed mask, the weight is counted exactly `card * (card - 1)` times. -/
private theorem short_sum_ordered_distinct_members_eq_card_mul_pred {n : ℕ}
    (mask : MutationMask n) (weight : ℝ) :
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        if i ∈ mask ∧ j ∈ mask then weight else 0) =
      (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * weight := by
  classical
  have hinner : ∀ i : Fin n,
      (∑ j ∈ (Finset.univ.erase i),
          if i ∈ mask ∧ j ∈ mask then weight else 0) =
        if i ∈ mask then ((mask.card - 1 : ℕ) : ℝ) * weight else 0 := by
    intro i
    by_cases hi : i ∈ mask
    · calc
        (∑ j ∈ (Finset.univ.erase i),
            if i ∈ mask ∧ j ∈ mask then weight else 0) =
            ∑ j ∈ (Finset.univ.erase i), if j ∈ mask then weight else 0 := by
              simp [hi]
        _ = ∑ j ∈ (mask.erase i), weight := by
              have hfilter :
                  (Finset.univ.erase i).filter (fun j : Fin n => j ∈ mask) =
                    mask.erase i := by
                ext j
                simp [Finset.mem_erase]
              rw [← hfilter]
              exact (Finset.sum_filter (fun j : Fin n => j ∈ mask)
                (fun _j : Fin n => weight)).symm
        _ = ((mask.erase i).card : ℝ) * weight := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((mask.card - 1 : ℕ) : ℝ) * weight := by
              rw [Finset.card_erase_of_mem hi]
        _ = if i ∈ mask then ((mask.card - 1 : ℕ) : ℝ) * weight else 0 := by
              simp [hi]
    · simp [hi]
  calc
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        if i ∈ mask ∧ j ∈ mask then weight else 0) =
        ∑ i : Fin n,
          if i ∈ mask then ((mask.card - 1 : ℕ) : ℝ) * weight else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hinner i
    _ = ∑ i ∈ mask, ((mask.card - 1 : ℕ) : ℝ) * weight := by
      exact Finset.sum_ite_mem_eq mask
        (fun _i : Fin n => ((mask.card - 1 : ℕ) : ℝ) * weight)
    _ = (mask.card : ℝ) * (((mask.card - 1 : ℕ) : ℝ) * weight) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * weight := by
      ring

/-- Exact aggregate short pair mass, with no change to the original mask law. -/
private theorem orderedDistinctShortPairMass_eq_truncatedSecondFactorialRadiusMoment
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    law.orderedDistinctShortPairMass b =
      law.truncatedSecondFactorialRadiusMoment (b - 1) := by
  classical
  rw [law.truncatedSecondFactorialRadiusMoment_eq_short_mask_sum b]
  unfold orderedDistinctShortPairMass shortRadiusPairFlipMass
  calc
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
          if i ∈ mask ∧ j ∈ mask then law.weight mask else 0) =
        ∑ i : Fin n, ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
          ∑ j ∈ (Finset.univ.erase i),
            if i ∈ mask ∧ j ∈ mask then law.weight mask else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
          ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
            if i ∈ mask ∧ j ∈ mask then law.weight mask else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ mask ∈ shortRadiusMaskEvent (n := n) b,
          (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
      apply Finset.sum_congr rfl
      intro mask hm
      exact short_sum_ordered_distinct_members_eq_card_mul_pred mask (law.weight mask)

/-- The aggregate mass consists of `n(n-1)` equal ordered-pair masses. -/
private theorem orderedDistinctShortPairMass_eq_n_mul_pred_mul_mass
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (b : ℕ)
    (i j : Fin n) (hij : i ≠ j) :
    law.orderedDistinctShortPairMass b =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * law.shortRadiusPairFlipMass b i j := by
  classical
  unfold orderedDistinctShortPairMass
  calc
    (∑ a : Fin n, ∑ c ∈ (Finset.univ.erase a), law.shortRadiusPairFlipMass b a c) =
        ∑ a : Fin n, ∑ _c ∈ (Finset.univ.erase a),
          law.shortRadiusPairFlipMass b i j := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      have hca : c ≠ a := (Finset.mem_erase.mp hc).1
      exact law.shortRadiusPairFlipMass_eq_of_distinct b a c i j (Ne.symm hca) hij
    _ = ∑ _a : Fin n,
        ((n - 1 : ℕ) : ℝ) * law.shortRadiusPairFlipMass b i j := by
      apply Finset.sum_congr rfl
      intro a ha
      have hcard : (Finset.univ.erase a).card = n - 1 := by simp
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (n : ℝ) * (((n - 1 : ℕ) : ℝ) * law.shortRadiusPairFlipMass b i j) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * law.shortRadiusPairFlipMass b i j := by
      ring

/-- Exact distinct-pair mass in the strict short-radius event.
The truncation at `b - 1` is valid even for `b = 0`, since the sole extra
radius-zero factorial summand is zero. This is an *unconditional* identity. -/
theorem shortRadiusPairFlipMass_eq_truncatedSecondFactorialRadiusMoment_div
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (b : ℕ) (i j : Fin n) (hij : i ≠ j) :
    law.shortRadiusPairFlipMass b i j =
      law.truncatedSecondFactorialRadiusMoment (b - 1) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  have hsum := law.orderedDistinctShortPairMass_eq_truncatedSecondFactorialRadiusMoment b
  have hnorm := law.orderedDistinctShortPairMass_eq_n_mul_pred_mul_mass b i j hij
  have hmul :
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * law.shortRadiusPairFlipMass b i j =
        law.truncatedSecondFactorialRadiusMoment (b - 1) :=
    hnorm.symm.trans hsum
  have hnpos : 0 < n := by omega
  have hpredpos : 0 < n - 1 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hpred0 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpredpos)
  have hden0 : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≠ 0 := mul_ne_zero hn0 hpred0
  apply (eq_div_iff hden0).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Short-radius pair-flip mass is bounded by the cutoff-scaled *first*
radius moment; the factor `b-1` cannot be removed using this estimate. -/
theorem shortRadiusPairFlipMass_le_cutoffMeanRadius_div
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (b : ℕ) (i j : Fin n) (hij : i ≠ j) :
    law.shortRadiusPairFlipMass b i j ≤
      (((b - 1 : ℕ) : ℝ) * law.meanRadius) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  rw [law.shortRadiusPairFlipMass_eq_truncatedSecondFactorialRadiusMoment_div
    hn b i j hij]
  have hposn : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hpospred : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ) :=
    mul_pos hposn hpospred
  have hmoment := law.truncatedSecondFactorialRadiusMoment_le_cutoff_mul_meanRadius
    (b - 1)
  apply (div_le_div_iff₀ hden hden).2
  exact mul_le_mul_of_nonneg_right hmoment hden.le

/-- The accepted pivot's `j`-flip slice is contained in the unconditional
short-radius joint-flip event for the pivot `i` and coordinate `j`. -/
theorem shortPivotRemainderEvent_coordinateSlice_mass_le_shortRadiusPairFlipMass
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i j : Fin n) :
    law.maskEventMass
        (secondCoordinateSlice (shortPivotRemainderEvent w x b i) j) ≤
      law.shortRadiusPairFlipMass b i j := by

  classical
  have hsub :
      secondCoordinateSlice (shortPivotRemainderEvent w x b i) j ⊆
        (shortRadiusMaskEvent (n := n) b).filter
          (fun mask : MutationMask n => i ∈ mask ∧ j ∈ mask) := by
    intro mask hmask
    have hdata := Finset.mem_filter.mp hmask
    have hrest : mask ∈ shortAcceptedPivotEvent w x b i :=
      (Finset.mem_erase.mp hdata.1).2
    have hshort : mask ∈ shortRadiusMaskEvent (n := n) b := by
      unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
      exact (Finset.mem_filter.mp hrest).1
    have hpivot : mask ∈ acceptedLeftmostZeroEvent w x i := by
      unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
      exact (Finset.mem_filter.mp hrest).2
    have him : i ∈ mask :=
      acceptedLeftmostZeroEvent_supports_pivot w x i mask hpivot
    exact Finset.mem_filter.mpr ⟨hshort, him, hdata.2⟩
  calc
    law.maskEventMass
        (secondCoordinateSlice (shortPivotRemainderEvent w x b i) j) ≤
        law.maskEventMass
          ((shortRadiusMaskEvent (n := n) b).filter
            (fun mask : MutationMask n => i ∈ mask ∧ j ∈ mask)) :=
          law.maskEventMass_mono hsub
    _ = law.shortRadiusPairFlipMass b i j := by
      unfold maskEventMass shortRadiusPairFlipMass
      rw [Finset.sum_filter]

/-- A radius-sensitive accepted-pivot loss budget. The only relaxation of
acceptance is the final comparison to an unconditional joint-flip event.
In particular, no conditional-radius law is substituted for `law`. -/
theorem shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (hi : x i = false)
    (hg : ∀ j, 0 ≤ g j) :
    law.acceptedEventFlippedOneLoss
        (shortPivotRemainderEvent w x b i) g x ≤
      (law.truncatedSecondFactorialRadiusMoment (b - 1) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
        (∑ j ∈ onePositions x, g j) := by

  classical
  rw [law.acceptedEventFlippedOneLoss_eq_coordinateSlices]
  let coeff : ℝ :=
    law.truncatedSecondFactorialRadiusMoment (b - 1) /
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ))
  calc
    (∑ j ∈ onePositions x,
        g j * law.maskEventMass
          (secondCoordinateSlice (shortPivotRemainderEvent w x b i) j)) ≤
        ∑ j ∈ onePositions x, g j * law.shortRadiusPairFlipMass b i j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (law.shortPivotRemainderEvent_coordinateSlice_mass_le_shortRadiusPairFlipMass
          w x b i j) (hg j)
    _ = ∑ j ∈ onePositions x, g j * coeff := by
      apply Finset.sum_congr rfl
      intro j hj
      have hxj : x j = true := (mem_onePositions_iff x j).1 hj
      have hij : i ≠ j := by
        intro heq
        subst j
        simp [hi] at hxj
      rw [law.shortRadiusPairFlipMass_eq_truncatedSecondFactorialRadiusMoment_div
        hn b i j hij]
    _ = coeff * (∑ j ∈ onePositions x, g j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Replacing the short factorial moment by `(b-1) * χ` produces a
first-moment-only bound for any fixed cutoff, but the factor `b-1` may
prevent the desired sharp drift estimate. -/
theorem shortPivotRemainderEvent_flippedOneLoss_le_cutoffMeanBudget
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (hi : x i = false)
    (hg : ∀ j, 0 ≤ g j) :
    law.acceptedEventFlippedOneLoss
        (shortPivotRemainderEvent w x b i) g x ≤
      (((b - 1 : ℕ) : ℝ) * law.meanRadius /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
        (∑ j ∈ onePositions x, g j) := by

  have hbase := law.shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
    hn w g x b i hi hg
  have hposn : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hpospred : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hden : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ) :=
    mul_pos hposn hpospred
  have hmoment := law.truncatedSecondFactorialRadiusMoment_le_cutoff_mul_meanRadius
    (b - 1)
  have hcoeff :
      law.truncatedSecondFactorialRadiusMoment (b - 1) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤
      ((b - 1 : ℕ) : ℝ) * law.meanRadius /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
    apply (div_le_div_iff₀ hden hden).2
    exact mul_le_mul_of_nonneg_right hmoment hden.le
  have hsum : 0 ≤ ∑ j ∈ onePositions x, g j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hg j
  exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hsum)

/-- Applying the proven Stage-93 singleton/pivot/tail decomposition to the
proposed per-pivot moment budgets gives an *explicit* global drift envelope.
It may be negative; it does not establish sharp mean-only runtime bounds. -/
theorem linearErrorPotential_drift_ge_shortPairMomentBudget_sub_tailMeanRadius
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (hg : ∀ j, 0 ≤ g j) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) -
      (∑ _i ∈ zeroPositions x,
        (law.truncatedSecondFactorialRadiusMoment (b - 1) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
          (∑ j ∈ onePositions x, g j)) -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) ≤
      driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x := by

  have hpos : 0 < n := by omega
  let budget : Fin n → ℝ := fun _ =>
    (law.truncatedSecondFactorialRadiusMoment (b - 1) /
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
      (∑ j ∈ onePositions x, g j)
  have hbudget : ∀ i ∈ zeroPositions x,
      law.acceptedEventFlippedOneLoss
        (shortPivotRemainderEvent w x b i) g x ≤ budget i := by
    intro i hi
    exact law.shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
      hn w g x b i ((mem_zeroPositions x i).1 hi) hg
  simpa only [budget] using
    (law.linearErrorPotential_drift_ge_singleton_sub_pivotBudgets_sub_tailMeanRadius
      hpos w g hw x b hb hg budget hbudget)

end StaticUnaryUnbiasedMutation
end ECRuntime
