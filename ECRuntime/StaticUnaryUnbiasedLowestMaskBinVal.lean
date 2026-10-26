import ECRuntime.StaticUnaryUnbiasedHighestMaskPivot
import ECRuntime.StaticUnaryUnbiasedShortRadiusPivot
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 99 proof batch 1: minimum-index acceptance for BinVal-like weights

Coordinate 0 is the MOST important bit in this repository. Stage 98's
maximum-index classes are exact first-moment bookkeeping, but their pivot
does not determine acceptance. The minimum-index flipped coordinate does
determine acceptance on strictly superincreasing positive objectives.

These are the nine user-approved Stage 99 propositions. Their proof bodies are
strict-compilation candidates and the module remains outside `ECRuntime.lean`
until the focused build and integration regression gates pass.
-/

/-- Original-law masks whose minimum numerical flipped index is `i`.
The empty mask has no pivot. -/
noncomputable def lowestMaskEvent {n : Nat} (i : Fin n) :
    Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (fun mask =>
    i ∈ mask ∧ ∀ j ∈ mask, i.val ≤ j.val)

/-- Strict superincreasing positive linear weights in the repository's
reversed indexing convention. For each `i`, its coefficient exceeds the
total coefficient of every *less important* coordinate `j > i`.
Geometric BinVal weights are a non-vacuous instance. -/
def SuperincreasingLinearWeights {n : Nat} (w : Fin n → Real) : Prop :=
  PositiveLinearWeights w ∧
    ∀ i : Fin n,
      (∑ j ∈ (Finset.univ.filter (fun j : Fin n => i.val < j.val)), w j) < w i

/-- The minimum-index class is characterized by one flipped pivot and
absence of flipped coordinates of greater objective importance. -/
theorem mem_lowestMaskEvent_iff {n : Nat} (i : Fin n)
    (mask : MutationMask n) :
    mask ∈ lowestMaskEvent i ↔
      i ∈ mask ∧ ∀ j ∈ mask, i.val ≤ j.val := by
  classical
  simp [lowestMaskEvent]

/-- The assigned minimum pivot belongs to the mutation mask. -/
theorem lowestMaskEvent_supports_pivot {n : Nat} (i : Fin n)
    (mask : MutationMask n) (hm : mask ∈ lowestMaskEvent i) :
    i ∈ mask := by
  exact (mem_lowestMaskEvent_iff i mask).mp hm |>.1

/-- Different minimum-index classes are disjoint, including `n = 0`. -/
theorem lowestMaskEvent_disjoint {n : Nat} (i j : Fin n)
    (hij : i ≠ j) :
    Disjoint (lowestMaskEvent i) (lowestMaskEvent j) := by
  classical
  rw [Finset.disjoint_left]
  intro mask hi hj
  obtain ⟨him, hib⟩ := (mem_lowestMaskEvent_iff i mask).mp hi
  obtain ⟨hjm, hjb⟩ := (mem_lowestMaskEvent_iff j mask).mp hj
  have heq : i = j := Fin.ext (Nat.le_antisymm (hib j hjm) (hjb i him))
  exact hij heq

/-- Every nonempty mask appears exactly once, with no hypothesis on the
mutation distribution or the selected potential. -/
theorem lowestMaskEvent_partition_sum {n : Nat}
    (F : MutationMask n → Real) :
    (Finset.univ.sum (fun i : Fin n =>
      (lowestMaskEvent i).sum F)) =
    (Finset.univ.sum (fun mask : MutationMask n =>
      if mask = (∅ : MutationMask n) then 0 else F mask)) := by
  classical
  have hexists (mask : MutationMask n) (hne : mask ≠ ∅) :
      ∃ i : Fin n, mask ∈ lowestMaskEvent i := by
    have hn : mask.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    let i : Fin n := mask.min' hn
    refine ⟨i, (mem_lowestMaskEvent_iff i mask).mpr ⟨Finset.min'_mem mask hn, ?_⟩⟩
    intro j hj
    change i ≤ j
    exact Finset.min'_le mask j hj
  have hunique (mask : MutationMask n) (i j : Fin n)
      (hi : mask ∈ lowestMaskEvent i) (hj : mask ∈ lowestMaskEvent j) :
      i = j := by
    obtain ⟨him, hib⟩ := (mem_lowestMaskEvent_iff i mask).mp hi
    obtain ⟨hjm, hjb⟩ := (mem_lowestMaskEvent_iff j mask).mp hj
    exact Fin.ext (Nat.le_antisymm (hib j hjm) (hjb i him))
  calc
    (∑ i : Fin n, ∑ mask ∈ lowestMaskEvent i, F mask) =
        ∑ mask : MutationMask n, ∑ i : Fin n,
          if mask ∈ lowestMaskEvent i then F mask else 0 := by
      calc
        (∑ i : Fin n, ∑ mask ∈ lowestMaskEvent i, F mask) =
            ∑ i : Fin n, ∑ mask : MutationMask n,
              if mask ∈ lowestMaskEvent i then F mask else 0 := by
                apply Finset.sum_congr rfl
                intro i _
                exact (Finset.sum_ite_mem_eq (lowestMaskEvent i) F).symm
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ mask : MutationMask n,
          if mask = (∅ : MutationMask n) then 0 else F mask := by
      apply Finset.sum_congr rfl
      intro mask _
      by_cases he : mask = (∅ : MutationMask n)
      · subst mask
        simp [lowestMaskEvent]
      · obtain ⟨i, hi⟩ := hexists mask he
        have hequiv (j : Fin n) : mask ∈ lowestMaskEvent j ↔ j = i := by
          constructor
          · intro hj
            exact hunique mask j i hj hi
          · intro hj
            subst j
            exact hi
        calc
          (∑ j : Fin n,
              if mask ∈ lowestMaskEvent j then F mask else 0) =
              ∑ j : Fin n, if j = i then F mask else 0 := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : j = i
                · subst j
                  simp [hi]
                · have hjnot : mask ∉ lowestMaskEvent j :=
                    fun hmem => hj ((hequiv j).mp hmem)
                  simp [hjnot, hj]
          _ = F mask := by simp
          _ = if mask = (∅ : MutationMask n) then 0 else F mask := by
                simp [he]

/-- Less important positions form a finite interval of length `n-1-i`. -/
private theorem card_upperFin {n : Nat} (i : Fin n) :
    ((Finset.univ.filter (fun j : Fin n => i.val < j.val)).card) =
      n - 1 - i.val := by
  classical
  let upper : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => i.val < j.val)
  change upper.card = n - 1 - i.val
  have hi_lt : i.val < n := i.isLt
  refine Finset.card_eq_of_bijective (s := upper)
    (fun j hj => (⟨i.val + 1 + j, by omega⟩ : Fin n)) ?_ ?_ ?_
  · intro j hj
    have hgt : i.val < j.val := (Finset.mem_filter.mp hj).2
    refine ⟨j.val - i.val - 1, by omega, ?_⟩
    apply Fin.ext
    -- Normalize the value of the dependent `Fin` constructor first.
    -- The bijection API may orient this inverse equality either way.
    first
    | change j.val = i.val + 1 + (j.val - i.val - 1)
    | change i.val + 1 + (j.val - i.val - 1) = j.val
    omega
  · intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    -- The bijection's domain is a natural-number interval, not `Fin n`.
    change i.val < i.val + 1 + j
    omega
  · intro j k hj hk heq
    have hval := congrArg Fin.val heq
    change i.val + 1 + j = i.val + 1 + k at hval
    omega

/-- Choosing the remaining `k-1` flipped bits above the minimum pivot. -/
private theorem lowestMaskEvent_radius_card {n : Nat}
    (i : Fin n) (k : Nat) (hk : 1 ≤ k) :
    ((lowestMaskEvent i).filter (fun mask => mask.card = k)).card =
      Nat.choose (n - 1 - i.val) (k - 1) := by
  classical
  let upper : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => i.val < j.val)
  have hc : upper.card = n - 1 - i.val := card_upperFin i
  have hcount :
      (Finset.powersetCard (k - 1) upper).card =
        ((lowestMaskEvent i).filter (fun mask => mask.card = k)).card := by
    refine Finset.card_bij (fun mask _ => insert i mask) ?_ ?_ ?_
    · intro mask hm
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hm
      have hinot : i ∉ mask := by
        intro hi
        have hupper : i ∈ upper := hsub hi
        have hlt : i.val < i.val := (Finset.mem_filter.mp hupper).2
        omega
      have hsize : (insert i mask).card = k := by
        rw [Finset.card_insert_of_notMem hinot, hcard]
        omega
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_lowestMaskEvent_iff i (insert i mask)).mpr
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
        have hs : i ∈ upper := hsub hi
        have hh := (Finset.mem_filter.mp hs).2
        omega
      have hno' : i ∉ mask' := by
        intro hi
        have hsub := (Finset.mem_powersetCard.mp hm').1
        have hs : i ∈ upper := hsub hi
        have hh := (Finset.mem_filter.mp hs).2
        omega
      have herase := congrArg (fun s : Finset (Fin n) => s.erase i) heq
      simpa [hno, hno'] using herase
    · intro mask hm
      obtain ⟨hmask, hcard⟩ := Finset.mem_filter.mp hm
      obtain ⟨hi, hbound⟩ := (mem_lowestMaskEvent_iff i mask).mp hmask
      refine ⟨mask.erase i, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro j hj
          have hne : j ≠ i := (Finset.mem_erase.mp hj).1
          have hjm : j ∈ mask := (Finset.mem_erase.mp hj).2
          have hle : i.val ≤ j.val := hbound j hjm
          have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h.symm)
          have hlt : i.val < j.val := by omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        · rw [Finset.card_erase_of_mem hi, hcard]
      · exact Finset.insert_erase hi
  calc
    ((lowestMaskEvent i).filter (fun mask => mask.card = k)).card =
        (Finset.powersetCard (k - 1) upper).card := hcount.symm
    _ = Nat.choose (n - 1 - i.val) (k - 1) := by
      rw [Finset.card_powersetCard, hc]

/-- A radius-k mask with minimum flipped index `i` chooses its remaining
`k-1` bits from exactly `n-1-i.val` less important indices. This is a
*denominator-free* original-law identity. Only `1 ≤ k ≤ n` is asserted. -/
theorem lowestMaskEvent_radius_choose_mass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) (k : Nat)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (Nat.choose n k : Real) *
      law.maskEventMass ((lowestMaskEvent i).filter
        (fun mask => mask.card = k)) =
    (Nat.choose (n - 1 - i.val) (k - 1) : Real) * law.radiusMass k := by
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
      ((lowestMaskEvent i).filter (fun mask => mask.card = k)) =
      (Nat.choose (n - 1 - i.val) (k - 1) : Real) * law.weight base := by
    unfold maskEventMass
    calc
      (∑ mask ∈ (lowestMaskEvent i).filter (fun mask => mask.card = k),
          law.weight mask) =
          (((lowestMaskEvent i).filter (fun mask => mask.card = k)).card : Real) *
            law.weight base :=
            hmass _ (fun mask hm => (Finset.mem_filter.mp hm).2)
      _ = (Nat.choose (n - 1 - i.val) (k - 1) : Real) * law.weight base := by
        rw [lowestMaskEvent_radius_card i k hk]
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

/-- Reindexing by the acceptance-determining minimum pivot still consumes
exactly the FIRST moment, not a pair-flip factorial moment. -/
theorem sum_lowestMaskEvent_radius_charge_eq_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) :
    (Finset.univ.sum (fun i : Fin n =>
      (lowestMaskEvent i).sum (fun mask =>
        (mask.card : Real) * law.weight mask))) = law.meanRadius := by
  classical
  rw [lowestMaskEvent_partition_sum]
  rw [law.meanRadius_eq_sum_mask_card_weight]
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hm : mask = (∅ : MutationMask n)
  · subst mask
    simp
  · simp [hm]

/-- Every flip contribution lies between minus and plus the coefficient. -/
private theorem flipContribution_weight_bounds {n : Nat}
    (w : Fin n → Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (j : Fin n) :
    -w j ≤ flipContribution w x mask j ∧
      flipContribution w x mask j ≤ w j := by
  unfold flipContribution
  split_ifs <;> constructor <;> linarith [hw j]

/-- Contributions outside the minimum pivot are dominated by the total
weight of the less important coordinates, in both signs. -/
private theorem lowestMaskEvent_tail_flip_bounds {n : Nat}
    (w : Fin n → Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hm : mask ∈ lowestMaskEvent i) :
    -(∑ j ∈ (Finset.univ.filter (fun j : Fin n => i.val < j.val)), w j) ≤
      ∑ j ∈ (Finset.univ.erase i), flipContribution w x mask j ∧
    (∑ j ∈ (Finset.univ.erase i), flipContribution w x mask j) ≤
      ∑ j ∈ (Finset.univ.filter (fun j : Fin n => i.val < j.val)), w j := by
  classical
  let upper : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => i.val < j.val)
  let r : Fin n → Real := fun j => if i.val < j.val then w j else 0
  have hr_eq : (∑ j ∈ Finset.univ.erase i, r j) = ∑ j ∈ upper, w j := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      r (Finset.mem_univ i)
    have hre : r i = 0 := by simp [r]
    rw [hre, add_zero] at h
    calc
      (∑ j ∈ Finset.univ.erase i, r j) = ∑ j : Fin n, r j := h
      _ = ∑ j ∈ upper, w j := by
        simp [r, upper, Finset.sum_filter]
  have hper (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      -r j ≤ flipContribution w x mask j ∧
        flipContribution w x mask j ≤ r j := by
    by_cases hlt : i.val < j.val
    · have hrj : r j = w j := by
        change (if i.val < j.val then w j else 0) = w j
        exact if_pos hlt
      rw [hrj]
      exact flipContribution_weight_bounds w hw x mask j
    · have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      have hneval : j.val ≠ i.val := by
        intro heq
        exact hne (Fin.ext heq)
      have hjlt : j.val < i.val := by omega
      have hjnot : j ∉ mask := by
        intro hjm
        have hbound := ((mem_lowestMaskEvent_iff i mask).mp hm).2 j hjm
        omega
      have hrj : r j = 0 := by
        change (if i.val < j.val then w j else 0) = 0
        exact if_neg hlt
      have hflip : flipContribution w x mask j = 0 := by
        simp [flipContribution, hjnot]
      rw [hrj, hflip]
      constructor <;> norm_num
  change -(∑ j ∈ upper, w j) ≤
      ∑ j ∈ Finset.univ.erase i, flipContribution w x mask j ∧
    (∑ j ∈ Finset.univ.erase i, flipContribution w x mask j) ≤
      ∑ j ∈ upper, w j
  constructor
  · calc
      -(∑ j ∈ upper, w j) =
          ∑ j ∈ Finset.univ.erase i, -r j := by
            simp only [Finset.sum_neg_distrib, hr_eq]
      _ ≤ ∑ j ∈ Finset.univ.erase i,
          flipContribution w x mask j := by
            apply Finset.sum_le_sum
            intro j hj
            exact (hper j hj).1
  · calc
      (∑ j ∈ Finset.univ.erase i, flipContribution w x mask j) ≤
          ∑ j ∈ Finset.univ.erase i, r j := by
            apply Finset.sum_le_sum
            intro j hj
            exact (hper j hj).2
      _ = ∑ j ∈ upper, w j := hr_eq

/-- On a strictly superincreasing objective, the *only* relevant acceptance
bit of a nonempty mask is its least numerical (most important) flipped
coordinate. This is an IFF, not merely a sufficient condition. -/
theorem superincreasing_accepts_iff_lowest_pivot_zero {n : Nat}
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hm : mask ∈ lowestMaskEvent i) :
    Accepts (linearFitness w) x (mutateWithMask x mask) ↔ x i = false := by
  classical
  obtain ⟨him, _⟩ := (mem_lowestMaskEvent_iff i mask).mp hm
  have hsplit :
      (∑ j : Fin n, flipContribution w x mask j) =
        flipContribution w x mask i +
          ∑ j ∈ (Finset.univ.erase i), flipContribution w x mask j := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (flipContribution w x mask) (Finset.mem_univ i)
    linarith
  have hbounds := lowestMaskEvent_tail_flip_bounds w hw.1 x i mask hm
  have hdominates := hw.2 i
  cases hxi : x i with
  | false =>
      have hpivot : flipContribution w x mask i = w i := by
        simp [flipContribution, him, hxi]
      have hpositive : 0 < ∑ j : Fin n, flipContribution w x mask j := by
        rw [hsplit, hpivot]
        linarith [hbounds.1, hdominates]
      have haccept := (accepts_linearFitness_iff_flipContribution_nonneg
        w x mask).2 (le_of_lt hpositive)
      simpa [hxi] using haccept
  | true =>
      have hpivot : flipContribution w x mask i = -w i := by
        simp [flipContribution, him, hxi]
      have hnegative : (∑ j : Fin n, flipContribution w x mask j) < 0 := by
        rw [hsplit, hpivot]
        linarith [hbounds.2, hdominates]
      have hrejected : ¬ Accepts (linearFitness w) x
          (mutateWithMask x mask) := by
        intro haccept
        have hnonneg := (accepts_linearFitness_iff_flipContribution_nonneg
          w x mask).1 haccept
        linarith
      simpa [hxi] using hrejected

-- `Finset.filter` needs decidability of `Accepts` when the proposition is
-- elaborated. A proof-local `classical` cannot supply this instance.
-- Keep the classical instance local to this one statement.
section AcceptedLowestMaskDecidability
attribute [local instance] Classical.propDecidable

/-- Under superincreasing weights, the *original-law* accepted mask mass
at a minimum-index pivot equals its entire mass if `x i = false`, and is
zero otherwise. There is no conditioning on a flipped bit or radius. -/
theorem accepted_lowestMaskEvent_mass_eq_if_zero {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    law.maskEventMass ((lowestMaskEvent i).filter (fun mask =>
      Accepts (linearFitness w) x (mutateWithMask x mask))) =
      if x i = false then law.maskEventMass (lowestMaskEvent i) else 0 := by
  classical
  by_cases hi : x i = false
  · have heq :
        (lowestMaskEvent i).filter (fun mask =>
          Accepts (linearFitness w) x (mutateWithMask x mask)) =
        lowestMaskEvent i := by
          apply Finset.ext
          intro mask
          constructor
          · intro h
            exact (Finset.mem_filter.mp h).1
          · intro h
            exact Finset.mem_filter.mpr
              ⟨h, (superincreasing_accepts_iff_lowest_pivot_zero
                w hw x i mask h).2 hi⟩
    rw [heq]
    simp [hi]
  · have heq :
        (lowestMaskEvent i).filter (fun mask =>
          Accepts (linearFitness w) x (mutateWithMask x mask)) =
        ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro mask h
          obtain ⟨hmask, hacc⟩ := Finset.mem_filter.mp h
          exact hi ((superincreasing_accepts_iff_lowest_pivot_zero
            w hw x i mask hmask).1 hacc)
    rw [heq]
    simp [hi, maskEventMass]

end AcceptedLowestMaskDecidability

/-- Exact signed selected-potential drift over all masks becomes a sum over
minimum-index pivots that improve the objective. All contributions retain
their ORIGINAL probabilities and arbitrary real potential coefficients.
No claim of nonnegative one-step drift is made. -/
theorem acceptedEventWeightedPotentialDrop_eq_sum_lowest_zeros {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) :
    law.acceptedEventWeightedPotentialDrop
      (Finset.univ : Finset (MutationMask n)) w g x =
      ∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := by
  classical
  let F : MutationMask n → Real := fun mask =>
    law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask))
  have hnil : F (∅ : MutationMask n) = 0 := by
    simp [F, selectedAfterMask, elitistSelect, mutateWithMask_empty]
  have hpart := lowestMaskEvent_partition_sum (n := n) F
  have htotal : law.acceptedEventWeightedPotentialDrop
      (Finset.univ : Finset (MutationMask n)) w g x =
      ∑ i : Fin n,
        law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := by
    unfold acceptedEventWeightedPotentialDrop
    change (∑ mask : MutationMask n, F mask) =
      ∑ i : Fin n, ∑ mask ∈ lowestMaskEvent i, F mask
    calc
      (∑ mask : MutationMask n, F mask) =
          ∑ mask : MutationMask n,
            if mask = (∅ : MutationMask n) then 0 else F mask := by
              apply Finset.sum_congr rfl
              intro mask _
              by_cases he : mask = (∅ : MutationMask n)
              · subst mask
                simp [hnil]
              · simp [he]
      _ = ∑ i : Fin n, ∑ mask ∈ lowestMaskEvent i, F mask := hpart.symm
  have hreject (i : Fin n) (hi : x i ≠ false) :
      law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x = 0 := by
    unfold acceptedEventWeightedPotentialDrop
    apply Finset.sum_eq_zero
    intro mask hm
    have hno : ¬ Accepts (linearFitness w) x (mutateWithMask x mask) := by
      intro ha
      exact hi ((superincreasing_accepts_iff_lowest_pivot_zero
        w hw x i mask hm).1 ha)
    rw [linearErrorPotential_selected_drop_of_rejects w g x mask hno]
    ring
  calc
    law.acceptedEventWeightedPotentialDrop Finset.univ w g x =
        ∑ i : Fin n,
          law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := htotal
    _ = ∑ i ∈ zeroPositions x,
          law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := by
      unfold zeroPositions
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x i = false
      · simp [hi]
      · simp [hi, hreject i hi]

end StaticUnaryUnbiasedMutation
end ECRuntime
