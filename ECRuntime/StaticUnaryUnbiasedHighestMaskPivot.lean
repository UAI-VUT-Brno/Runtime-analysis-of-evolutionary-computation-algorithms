import ECRuntime.StaticUnaryUnbiasedResidualLossBudget
import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 98: highest-flipped-index first-moment accounting

These are the nine user-approved Stage 98 propositions. All sums use the original,
unconditioned mask law. The largest *numerical* index is merely a disjoint
accounting key, not the acceptance-determining most-important coordinate.

The results are an exact signed partition and a first-moment budget, not a
positive one-step drift theorem or the Doerr--Janett--Lengler runtime bound.
-/

/-- Original-law masks whose largest numerical flipped index is `i`.
The empty mask belongs to no event. -/
noncomputable def highestMaskEvent {n : Nat} (i : Fin n) :
    Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (fun mask =>
    i ∈ mask ∧ ∀ j ∈ mask, j.val ≤ i.val)

/-- A mask is assigned to `i` exactly when it flips `i` and no greater index. -/
theorem mem_highestMaskEvent_iff {n : Nat} (i : Fin n)
    (mask : MutationMask n) :
    mask ∈ highestMaskEvent i ↔
      i ∈ mask ∧ ∀ j ∈ mask, j.val ≤ i.val := by
  classical
  simp [highestMaskEvent]

/-- The assigned pivot is genuinely flipped; empty masks cannot occur. -/
theorem highestMaskEvent_supports_pivot {n : Nat} (i : Fin n)
    (mask : MutationMask n) (hm : mask ∈ highestMaskEvent i) :
    i ∈ mask := by
  exact (mem_highestMaskEvent_iff i mask).mp hm |>.1

/-- A mask cannot belong to two distinct highest-index classes. -/
private theorem highestMaskEvent_unique {n : Nat}
    (i j : Fin n) (mask : MutationMask n)
    (hi : mask ∈ highestMaskEvent i)
    (hj : mask ∈ highestMaskEvent j) : i = j := by
  obtain ⟨him, hib⟩ := (mem_highestMaskEvent_iff i mask).mp hi
  obtain ⟨hjm, hjb⟩ := (mem_highestMaskEvent_iff j mask).mp hj
  apply Fin.ext
  exact Nat.le_antisymm (hjb i him) (hib j hjm)

/-- Largest-coordinate classes are disjoint for unequal indices. -/
theorem highestMaskEvent_disjoint {n : Nat}
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (highestMaskEvent i) (highestMaskEvent j) := by
  classical
  rw [Finset.disjoint_left]
  intro mask hi hj
  exact hij (highestMaskEvent_unique i j mask hi hj)

/-- A nonempty mask has a highest-index class. -/
private theorem highestMaskEvent_exists {n : Nat}
    (mask : MutationMask n) (hmask : mask ≠ ∅) :
    ∃ i : Fin n, mask ∈ highestMaskEvent i := by
  classical
  have hn : mask.Nonempty := Finset.nonempty_iff_ne_empty.mpr hmask
  let i : Fin n := mask.max' hn
  have hmax : i ∈ mask ∧ ∀ j ∈ mask, j ≤ i :=
    (Finset.max'_eq_iff mask hn i).mp rfl
  refine ⟨i, (mem_highestMaskEvent_iff i mask).mpr ⟨hmax.1, ?_⟩⟩
  intro j hj
  exact hmax.2 j hj

/-- Every nonempty mask is counted once by the highest-pivot partition.
The empty mask is deliberately assigned contribution zero. -/
theorem highestMaskEvent_partition_sum {n : Nat}
    (F : MutationMask n -> Real) :
    (Finset.univ.sum (fun i : Fin n =>
      (highestMaskEvent i).sum F)) =
    (Finset.univ.sum (fun mask : MutationMask n =>
      if mask = (∅ : MutationMask n) then 0 else F mask)) := by
  classical
  calc
    (∑ i : Fin n, ∑ mask ∈ highestMaskEvent i, F mask) =
        ∑ mask : MutationMask n, ∑ i : Fin n,
          if mask ∈ highestMaskEvent i then F mask else 0 := by
      calc
        (∑ i : Fin n, ∑ mask ∈ highestMaskEvent i, F mask) =
            ∑ i : Fin n, ∑ mask : MutationMask n,
              if mask ∈ highestMaskEvent i then F mask else 0 := by
                apply Finset.sum_congr rfl
                intro i _
                exact (Finset.sum_ite_mem_eq (highestMaskEvent i) F).symm
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ mask : MutationMask n,
          if mask = (∅ : MutationMask n) then 0 else F mask := by
      apply Finset.sum_congr rfl
      intro mask _
      by_cases he : mask = (∅ : MutationMask n)
      · subst mask
        simp [highestMaskEvent]
      · obtain ⟨i, hi⟩ := highestMaskEvent_exists mask he
        have hequiv (j : Fin n) : mask ∈ highestMaskEvent j ↔ j = i := by
          constructor
          · intro hj
            exact highestMaskEvent_unique j i mask hj hi
          · intro hj
            subst j
            exact hi
        calc
          (∑ j : Fin n,
              if mask ∈ highestMaskEvent j then F mask else 0) =
              ∑ j : Fin n, if j = i then F mask else 0 := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : j = i
                · subst j
                  simp [hi]
                · have hjnot : mask ∉ highestMaskEvent j :=
                    fun hmem => hj ((hequiv j).mp hmem)
                  simp [hjnot, hj]
          _ = F mask := by simp
          _ = if mask = (∅ : MutationMask n) then 0 else F mask := by
                simp [he]

/-- Total original-law mass of nonempty masks, including n=0 and p0>0. -/
theorem sum_highestMaskEvent_mass_eq_one_sub_empty {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) :
    (Finset.univ.sum (fun i : Fin n =>
      law.maskEventMass (highestMaskEvent i))) =
    1 - law.weight (∅ : MutationMask n) := by
  classical
  change (∑ i : Fin n, ∑ mask ∈ highestMaskEvent i, law.weight mask) = _
  rw [highestMaskEvent_partition_sum]
  have heq :
      (∑ mask : MutationMask n,
        if mask = (∅ : MutationMask n) then (0 : Real) else law.weight mask) =
      ∑ mask ∈ (Finset.univ.erase (∅ : MutationMask n)), law.weight mask := by
    calc
      (∑ mask : MutationMask n,
        if mask = (∅ : MutationMask n) then (0 : Real) else law.weight mask) =
          ∑ mask : MutationMask n,
            if mask ∈ (Finset.univ.erase (∅ : MutationMask n)) then
              law.weight mask else 0 := by
                apply Finset.sum_congr rfl
                intro mask _
                by_cases hm : mask = (∅ : MutationMask n) <;> simp [hm]
      _ = ∑ mask ∈ (Finset.univ.erase (∅ : MutationMask n)),
            law.weight mask := by
              exact Finset.sum_ite_mem_eq _ _
  rw [heq]
  have hsum := Finset.sum_erase_add
    (Finset.univ : Finset (MutationMask n)) law.weight (Finset.mem_univ ∅)
  rw [law.weight_sum] at hsum
  linarith

/-- The set of numerically smaller coordinates has exactly `i.val` members. -/
private theorem card_lowerFin {n : Nat} (i : Fin n) :
    ((Finset.univ.filter (fun j : Fin n => j.val < i.val)).card) = i.val := by
  classical
  let small : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => j.val < i.val)
  change small.card = i.val
  refine Finset.card_eq_of_bijective (s := small)
    (fun j hj => (⟨j, Nat.lt_trans hj i.isLt⟩ : Fin n)) ?_ ?_ ?_
  · intro j hj
    refine ⟨j.val, (Finset.mem_filter.mp hj).2, ?_⟩
    rfl
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  · intro j k hj hk heq
    exact congrArg Fin.val heq

/-- Radius-k highest-index classes are enumerated by (k-1)-subsets of
coordinates strictly below the pivot. This is a genuine finite bijection. -/
private theorem highestMaskEvent_radius_card {n : Nat}
    (i : Fin n) (k : Nat) (hk : 1 ≤ k) :
    ((highestMaskEvent i).filter (fun mask => mask.card = k)).card =
      Nat.choose i.val (k - 1) := by
  classical
  let small : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => j.val < i.val)
  have hc : small.card = i.val := card_lowerFin i
  have hcount :
      (Finset.powersetCard (k - 1) small).card =
        ((highestMaskEvent i).filter (fun mask => mask.card = k)).card := by
    refine Finset.card_bij (fun mask _ => insert i mask) ?_ ?_ ?_
    · intro mask hm
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hm
      have hinot : i ∉ mask := by
        intro hi
        have hsmall : i ∈ small := hsub hi
        have hlt : i.val < i.val := (Finset.mem_filter.mp hsmall).2
        omega
      have hsize : (insert i mask).card = k := by
        rw [Finset.card_insert_of_notMem hinot, hcard]
        omega
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_highestMaskEvent_iff i (insert i mask)).mpr
        constructor
        · simp
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact le_refl _
          · exact Nat.le_of_lt ((Finset.mem_filter.mp (hsub hj)).2)
      · exact hsize
    · intro mask hm mask' hm' heq
      have hno : i ∉ mask := by
        intro hi
        have hsub := (Finset.mem_powersetCard.mp hm).1
        have hs : i ∈ small := hsub hi
        have hh := (Finset.mem_filter.mp hs).2
        omega
      have hno' : i ∉ mask' := by
        intro hi
        have hsub := (Finset.mem_powersetCard.mp hm').1
        have hs : i ∈ small := hsub hi
        have hh := (Finset.mem_filter.mp hs).2
        omega
      have herase := congrArg (fun s : Finset (Fin n) => s.erase i) heq
      simpa [hno, hno'] using herase
    · intro mask hm
      obtain ⟨hmask, hcard⟩ := Finset.mem_filter.mp hm
      obtain ⟨hi, hbound⟩ := (mem_highestMaskEvent_iff i mask).mp hmask
      refine ⟨mask.erase i, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro j hj
          have hne : j ≠ i := (Finset.mem_erase.mp hj).1
          have hjm : j ∈ mask := (Finset.mem_erase.mp hj).2
          have hle : j.val ≤ i.val := hbound j hjm
          have hneval : j.val ≠ i.val := fun h => hne (Fin.ext h)
          have hlt : j.val < i.val := by omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        · rw [Finset.card_erase_of_mem hi, hcard]
      · exact Finset.insert_erase hi
  calc
    ((highestMaskEvent i).filter (fun mask => mask.card = k)).card =
        (Finset.powersetCard (k - 1) small).card := hcount.symm
    _ = Nat.choose i.val (k - 1) := by
      rw [Finset.card_powersetCard, hc]

/-- Exact binomial mass for a fixed radius k>=1 at pivot i.
We multiply by choose(n,k) rather than dividing, avoiding zero denominators
for boundary cases. The count is choose(i.val,k-1) in the repository's index
convention, because all other flipped positions are strictly smaller than i. -/
theorem highestMaskEvent_radius_choose_mass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) (k : Nat)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (Nat.choose n k : Real) *
      law.maskEventMass ((highestMaskEvent i).filter
        (fun mask => mask.card = k)) =
    (Nat.choose i.val (k - 1) : Real) * law.radiusMass k := by
  classical
  have hnon : (Finset.powersetCard k (Finset.univ : Finset (Fin n))).Nonempty := by
    exact Finset.powersetCard_nonempty_of_le (by simpa using hkn)
  obtain ⟨base, hb⟩ := hnon
  have hbcard : base.card = k := (Finset.mem_powersetCard.mp hb).2
  have hmass (s : Finset (MutationMask n))
      (hs : ∀ mask ∈ s, mask.card = k) :
      (∑ mask ∈ s, law.weight mask) =
        (s.card : Real) * law.weight base := by
    calc
      (∑ mask ∈ s, law.weight mask) =
          ∑ _mask ∈ s, law.weight base := by
            apply Finset.sum_congr rfl
            intro mask hm
            exact law.card_invariant ((hs mask hm).trans hbcard.symm)
      _ = (s.card : Real) * law.weight base := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hleft : law.maskEventMass
      ((highestMaskEvent i).filter (fun mask => mask.card = k)) =
      (Nat.choose i.val (k - 1) : Real) * law.weight base := by
    unfold maskEventMass
    calc
      (∑ mask ∈ (highestMaskEvent i).filter (fun mask => mask.card = k),
          law.weight mask) =
          (((highestMaskEvent i).filter (fun mask => mask.card = k)).card : Real) *
            law.weight base :=
            hmass _ (fun mask hm => (Finset.mem_filter.mp hm).2)
      _ = (Nat.choose i.val (k - 1) : Real) * law.weight base := by
        rw [highestMaskEvent_radius_card i k hk]
  have hright : law.radiusMass k =
      (Nat.choose n k : Real) * law.weight base := by
    unfold radiusMass
    calc
      (∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
        law.weight mask) =
          (((Finset.powersetCard k (Finset.univ : Finset (Fin n))).card : Real) *
            law.weight base) :=
            hmass _ (fun mask hm => (Finset.mem_powersetCard.mp hm).2)
      _ = (Nat.choose n k : Real) * law.weight base := by simp
  rw [hleft, hright]
  ring

/-- Exact radius-weighted first-moment partition. Each nonempty mask appears
once, so the right side is chi=E[K], not the second factorial moment. -/
theorem sum_highestMaskEvent_radius_charge_eq_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) :
    (Finset.univ.sum (fun i : Fin n =>
      (highestMaskEvent i).sum (fun mask =>
        (mask.card : Real) * law.weight mask))) = law.meanRadius := by
  classical
  rw [highestMaskEvent_partition_sum]
  rw [law.meanRadius_eq_sum_mask_card_weight]
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hm : mask = (∅ : MutationMask n)
  · subst mask
    simp
  · simp [hm]

/-- Any mask subevent, including a state-dependent acceptance event, consumes
no more than the unconditional first-moment mass. Event selection does NOT
change the law and we do not condition on a bit flip. -/
theorem sum_highestMaskEvent_restricted_radius_charge_le_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) :
    (Finset.univ.sum (fun i : Fin n =>
      ((highestMaskEvent i) ∩ event).sum (fun mask =>
        (mask.card : Real) * law.weight mask))) ≤ law.meanRadius := by
  classical
  calc
    (∑ i : Fin n, ∑ mask ∈ highestMaskEvent i ∩ event,
        (mask.card : Real) * law.weight mask) ≤
        ∑ i : Fin n, ∑ mask ∈ highestMaskEvent i,
          (mask.card : Real) * law.weight mask := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
            intro mask hm hn
            exact mul_nonneg (Nat.cast_nonneg _) (law.weight_nonneg mask)
    _ = law.meanRadius := law.sum_highestMaskEvent_radius_charge_eq_meanRadius

/-- An EXACT signed event partition of the actual elitist selected-potential
change. It does not discard accepted gains, nor assume positive drift. An
empty mask contributes zero to the selected change even if in `event`.
This is the bridge to the Stage 95--97 accepted gain/loss infrastructure. -/
theorem acceptedEventWeightedPotentialDrop_eq_sum_highestMaskEvent
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n -> Real) (x : BitString n) :
    law.acceptedEventWeightedPotentialDrop event w g x =
      (Finset.univ.sum (fun i : Fin n =>
        law.acceptedEventWeightedPotentialDrop
          ((highestMaskEvent i) ∩ event) w g x)) := by
  classical
  let f : MutationMask n → Real := fun mask =>
    law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask))
  have hnil : f (∅ : MutationMask n) = 0 := by
    simp [f, selectedAfterMask, elitistSelect, mutateWithMask_empty]
  have hpartition := highestMaskEvent_partition_sum (n := n)
    (fun mask => if mask ∈ event then f mask else 0)
  unfold acceptedEventWeightedPotentialDrop
  change (∑ mask ∈ event, f mask) =
    ∑ i : Fin n, ∑ mask ∈ highestMaskEvent i ∩ event, f mask
  calc
    (∑ mask ∈ event, f mask) =
        ∑ mask : MutationMask n, if mask ∈ event then f mask else 0 := by
          exact (Finset.sum_ite_mem_eq event f).symm
    _ = ∑ mask : MutationMask n,
          if mask = (∅ : MutationMask n) then 0 else
            if mask ∈ event then f mask else 0 := by
          apply Finset.sum_congr rfl
          intro mask _
          by_cases he : mask = (∅ : MutationMask n)
          · subst mask
            simp [hnil]
          · simp [he]
    _ = ∑ i : Fin n, ∑ mask ∈ highestMaskEvent i,
          if mask ∈ event then f mask else 0 := hpartition.symm
    _ = ∑ i : Fin n, ∑ mask ∈ highestMaskEvent i ∩ event, f mask := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_filter]
          congr 1

end StaticUnaryUnbiasedMutation
end ECRuntime
