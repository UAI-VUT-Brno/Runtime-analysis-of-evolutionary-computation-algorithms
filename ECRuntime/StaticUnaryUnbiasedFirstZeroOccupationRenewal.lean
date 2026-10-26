import ECRuntime.StaticUnaryUnbiasedFirstZeroResidence
import ECRuntime.FiniteTrajectory
import ECRuntime.LeadingOnesOccupationRenewal
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

section OccupationDecidability
attribute [local instance] Classical.propDecidable

/-!
# Stage 102: first-zero level entry and occupation renewal (PROOF CANDIDATE)

These nine propositions have been approved by the user. Their proof bodies
are drafted and require strict compiler verification on the user machine.
They remain outside the public ECRuntime root until integration.

Stage 101 proves a state-independent geometric exit probability q_i for any
visited BinVal first-zero level. This stage targets the missing global bridge:
exact-time occupation is a convolution of first-entry mass and geometric
residence. The last bound reduces the expected total occupation of a level to
its entry mass times n / p1, and isolates the still-open challenge of bounding
entry probabilities sharply. Nothing here establishes the mean-only sharp
n log n runtime theorem for general linear functions.
-/

/-- The prefix including `i` consists entirely of corrected (one) bits. -/
def firstZeroCorrectPrefixThrough {n : Nat}
    (x : BitString n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j.val ≤ i.val → x j = true

/-- Exact-time finite-state marginal, starting at `x`, of the genuine selected
static unary-unbiased transition; the original radius distribution is used. -/
noncomputable def firstZeroStateMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) : Nat → BitString n → Real
  | 0, z => if z = x then 1 else 0
  | t + 1, z =>
      ∑ y : BitString n,
        firstZeroStateMass law w x t y *
          (law.transition (linearFitness w)) y z

/-- Probability mass of occupying the exact first-zero level at time `t`. -/
noncomputable def firstZeroOccupationMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (i : Fin n) (t : Nat) : Real :=
  finiteEventMass (firstZeroStateMass law w x t)
    (fun z : BitString n => z ∈ firstZeroLevel i)

/-- Exact-time entry flow from OUTSIDE the first-zero level into it.
For `t=0`, entry means that the initial state already occupies the level.
The prefix/no-return lemmas ensure that each trajectory enters at most once. -/
noncomputable def firstZeroEntryMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (i : Fin n) : Nat → Real
  | 0 => if x ∈ firstZeroLevel i then 1 else 0
  | t + 1 =>
      ∑ z : BitString n,
        firstZeroStateMass law w x t z *
          finiteEventMass ((law.transition (linearFitness w)) z)
            (fun y : BitString n =>
              z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i)

/-- (1/9) An all-one prefix cannot be damaged by elitist selection on
strictly superincreasing linear weights, even outside a first-zero level. -/
theorem firstZeroCorrectPrefixThrough_selected_preserves {n : Nat}
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n)
    (hp : firstZeroCorrectPrefixThrough x i)
    (mask : MutationMask n) :
    firstZeroCorrectPrefixThrough
      (selectedAfterMask (linearFitness w) x mask) i := by
  intro j hj
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · have hjnot : j ∉ mask := by
      intro hjmask
      have hne : mask.Nonempty := ⟨j, hjmask⟩
      let m : Fin n := mask.min' hne
      have hm : mask ∈ lowestMaskEvent m := by
        apply (mem_lowestMaskEvent_iff m mask).2
        constructor
        · exact Finset.min'_mem mask hne
        · intro k hk
          change m ≤ k
          exact Finset.min'_le mask k hk
      have hmle : m ≤ j := Finset.min'_le mask j hjmask
      have hmi : m.val ≤ i.val := le_trans hmle hj
      have hone : x m = true := hp m hmi
      have hzero : x m = false :=
        (superincreasing_accepts_iff_lowest_pivot_zero
          w hw x m mask hm).1 hacc
      rw [hone] at hzero
      cases hzero
    change (elitistSelect (linearFitness w) x
      (mutateWithMask x mask)) j = true
    rw [elitistSelect_of_accepts _ _ _ hacc]
    simp [mutateWithMask, hjnot, hp j hj]
  · change (elitistSelect (linearFitness w) x
      (mutateWithMask x mask)) j = true
    rw [elitistSelect_of_rejects _ _ _ hacc]
    exact hp j hj

/-- (2/9) Exiting level `i` repairs its pivot as well as the entire earlier
prefix, even if the mutation also flips less-important coordinates. -/
theorem firstZeroAt_exit_correctPrefixThrough {n : Nat}
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask : MutationMask n)
    (hexit : selectedAfterMask (linearFitness w) x mask ∉ firstZeroLevel i) :
    firstZeroCorrectPrefixThrough
      (selectedAfterMask (linearFitness w) x mask) i := by
  have hprefix : firstZeroPrefixOnes
      (selectedAfterMask (linearFitness w) x mask) i :=
    firstZeroAt_selected_preserves_prefix w hw x i hx mask
  intro j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact hprefix j hlt
  · have hji : j = i := Fin.ext heq
    subst j
    by_cases hb : selectedAfterMask (linearFitness w) x mask i = false
    · exact False.elim (hexit ⟨hprefix, hb⟩)
    · cases hval : selectedAfterMask (linearFitness w) x mask i with
      | false => exact False.elim (hb hval)
      | true => rfl

/-- (3/9) A state with an already corrected prefix through `i` is not in
the first-zero level at `i`. -/
theorem firstZeroCorrectPrefixThrough_not_level {n : Nat}
    (x : BitString n) (i : Fin n)
    (hp : firstZeroCorrectPrefixThrough x i) :
    x ∉ firstZeroLevel i := by
  intro hlevel
  have hone : x i = true := hp i (le_refl _)
  have hzero : x i = false := hlevel.2
  rw [hone] at hzero
  cases hzero

/-- (4/9) The first-zero level cannot be re-entered after being exited,
including after any second mutation mask. -/
theorem firstZeroAt_no_return_two_steps {n : Nat}
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask₁ mask₂ : MutationMask n)
    (hexit : selectedAfterMask (linearFitness w) x mask₁ ∉ firstZeroLevel i) :
    selectedAfterMask (linearFitness w)
      (selectedAfterMask (linearFitness w) x mask₁) mask₂ ∉
        firstZeroLevel i := by
  have hfixed : firstZeroCorrectPrefixThrough
      (selectedAfterMask (linearFitness w) x mask₁) i :=
    firstZeroAt_exit_correctPrefixThrough w hw x i hx mask₁ hexit
  exact firstZeroCorrectPrefixThrough_not_level
    (selectedAfterMask (linearFitness w)
      (selectedAfterMask (linearFitness w) x mask₁) mask₂) i
    (firstZeroCorrectPrefixThrough_selected_preserves
      w hw _ i hfixed mask₂)

/-- (5/9) The actual transition kernel assigns zero one-step mass to
returning to a corrected first-zero level. -/
theorem firstZeroCorrectPrefixThrough_return_mass_eq_zero {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (z : BitString n) (i : Fin n)
    (hp : firstZeroCorrectPrefixThrough z i) :
    finiteEventMass ((law.transition (linearFitness w)) z)
      (fun y : BitString n => y ∈ firstZeroLevel i) = 0 := by
  classical
  change finiteEventMass
    (pushforwardWeight law.weight (selectedAfterMask (linearFitness w) z))
    (fun y : BitString n => y ∈ firstZeroLevel i) = 0
  rw [finiteEventMass_pushforwardWeight]
  unfold finiteEventMass
  apply Finset.sum_eq_zero
  intro mask _
  have hprefix : firstZeroCorrectPrefixThrough
      (selectedAfterMask (linearFitness w) z mask) i :=
    firstZeroCorrectPrefixThrough_selected_preserves w hw z i hp mask
  have hnot : selectedAfterMask (linearFitness w) z mask ∉
      firstZeroLevel i :=
    firstZeroCorrectPrefixThrough_not_level _ i hprefix
  have hnotmask : mask ∉
      ({m : MutationMask n |
        selectedAfterMask (linearFitness w) z m ∈ firstZeroLevel i} :
          Set (MutationMask n)) := hnot
  exact Set.indicator_of_notMem hnotmask law.weight

/-- (6/9) The exact-time marginal remains normalized at every horizon,
including `n=0` and radius-zero atoms. -/
theorem firstZeroStateMass_sum_eq_one {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (t : Nat) :
    (∑ z : BitString n, firstZeroStateMass law w x t z) = 1 := by
  classical
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  induction t with
  | zero =>
      simp [firstZeroStateMass]
  | succ t ih =>
      change (∑ z : BitString n,
          ∑ y : BitString n,
            firstZeroStateMass law w x t y *
              (law.transition (linearFitness w)) y z) = 1
      rw [Finset.sum_comm]
      calc
        (∑ y : BitString n, ∑ z : BitString n,
            firstZeroStateMass law w x t y *
              (law.transition (linearFitness w)) y z) =
          ∑ y : BitString n, firstZeroStateMass law w x t y *
            (∑ z : BitString n, (law.transition (linearFitness w)) y z) := by
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum]
        _ = ∑ y : BitString n, firstZeroStateMass law w x t y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hP.2 y, mul_one]
        _ = 1 := ih

/-- (7/9) Exact finite-state occupation renewal: the next occupation mass
is new entry mass plus previous occupation mass times the constant stay
probability, with no independence assumption about the evolving suffix. -/
theorem firstZeroOccupationMass_succ_eq_entry_add_stay {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (t : Nat) :
    firstZeroOccupationMass law w x i (t + 1) =
      firstZeroEntryMass law w x i (t + 1) +
        (1 - law.maskEventMass (lowestMaskEvent i)) *
          firstZeroOccupationMass law w x i t := by
  classical
  let P : TransitionMatrix (BitString n) := law.transition (linearFitness w)
  let L : Set (BitString n) := firstZeroLevel i
  let m : BitString n → Real := firstZeroStateMass law w x t
  let q : Real := law.maskEventMass (lowestMaskEvent i)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  have hstay (z : BitString n) (hz : z ∈ L) :
      finiteEventMass (P z) (fun y => y ∈ L) = 1 - q := by
    have hpart := finiteEventMass_add_compl (P z) (fun y => y ∈ L)
    have hexit := firstZeroAt_transition_exit_mass_eq law w hw z i hz
    change finiteEventMass (P z) (fun y => y ∉ L) = q at hexit
    rw [hP.2 z, hexit] at hpart
    linarith
  have hfubini :
      firstZeroOccupationMass law w x i (t + 1) =
        ∑ z : BitString n, m z * finiteEventMass (P z) (fun y => y ∈ L) := by
    change (∑ y : BitString n,
        if y ∈ L then (∑ z : BitString n, m z * P z y) else 0) =
      ∑ z : BitString n, m z *
        (∑ y : BitString n, if y ∈ L then P z y else 0)
    calc
      (∑ y : BitString n,
          if y ∈ L then (∑ z : BitString n, m z * P z y) else 0) =
        ∑ y : BitString n, ∑ z : BitString n,
          m z * (if y ∈ L then P z y else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ L <;> simp [hy]
      _ = ∑ z : BitString n, ∑ y : BitString n,
          m z * (if y ∈ L then P z y else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ z : BitString n, m z *
          (∑ y : BitString n, if y ∈ L then P z y else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
  rw [hfubini]
  have hpoint (z : BitString n) :
      m z * finiteEventMass (P z) (fun y => y ∈ L) =
        m z * finiteEventMass (P z) (fun y => z ∉ L ∧ y ∈ L) +
          (1 - q) * (if z ∈ L then m z else 0) := by
    by_cases hz : z ∈ L
    · have hentry : finiteEventMass (P z)
          (fun y => z ∉ L ∧ y ∈ L) = 0 := by
        simp [finiteEventMass, hz]
      rw [hentry, hstay z hz]
      simp only [mul_zero, zero_add, if_pos hz]
      ring
    · have hentry : finiteEventMass (P z)
          (fun y => z ∉ L ∧ y ∈ L) =
            finiteEventMass (P z) (fun y => y ∈ L) := by
        simp [finiteEventMass, hz]
      rw [hentry]
      simp [hz]
  calc
    (∑ z : BitString n, m z * finiteEventMass (P z) (fun y => y ∈ L)) =
      ∑ z : BitString n,
        (m z * finiteEventMass (P z) (fun y => z ∉ L ∧ y ∈ L) +
          (1 - q) * (if z ∈ L then m z else 0)) := by
        apply Finset.sum_congr rfl
        intro z _
        exact hpoint z
    _ = (∑ z : BitString n,
          m z * finiteEventMass (P z) (fun y => z ∉ L ∧ y ∈ L)) +
        (1 - q) * (∑ z : BitString n, if z ∈ L then m z else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = firstZeroEntryMass law w x i (t + 1) +
          (1 - law.maskEventMass (lowestMaskEvent i)) *
            firstZeroOccupationMass law w x i t := by
          rfl

/-- (8/9) Exact-time first-entry/residence convolution, exploiting the
Stage-101 suffix-independent geometric stay factor. -/
theorem firstZeroOccupationMass_eq_entry_convolution {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (t : Nat) :
    firstZeroOccupationMass law w x i t =
      ∑ s ∈ Finset.range (t + 1),
        firstZeroEntryMass law w x i s *
          (1 - law.maskEventMass (lowestMaskEvent i)) ^ (t - s) := by
  classical
  let a : Nat → Real := firstZeroOccupationMass law w x i
  let e : Nat → Real := firstZeroEntryMass law w x i
  let r : Real := 1 - law.maskEventMass (lowestMaskEvent i)
  have hzero : a 0 = e 0 := by
    change (∑ z : BitString n,
       if z ∈ firstZeroLevel i then (if z = x then (1 : Real) else 0) else 0) =
      if x ∈ firstZeroLevel i then (1 : Real) else 0
    calc
      (∑ z : BitString n,
          if z ∈ firstZeroLevel i then (if z = x then (1 : Real) else 0) else 0) =
        ∑ z : BitString n,
          if z = x then (if x ∈ firstZeroLevel i then (1 : Real) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z = x
          · subst z
            simp
          · simp [hz]
      _ = if x ∈ firstZeroLevel i then 1 else 0 := by simp
  have hrenew : HasScalarRenewalRecurrence e a r := by
    refine ⟨hzero, ?_⟩
    intro s
    exact firstZeroOccupationMass_succ_eq_entry_add_stay law w hw x i s
  exact scalarRenewalRecurrence_eq_convolution e a r hrenew t

/-- (9/9) Finite-horizon occupation reduces to entry probability mass
multiplied by the singleton-based residence cap `n / p1`.
This bound is intentionally not called a sharp runtime theorem: the
missing result is a sufficiently small sum of level-entry probabilities. -/
theorem firstZeroOccupationMass_horizon_le_entry_cap {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (T : Nat)
    (hp1 : 0 < law.oneBitMass) :
    (∑ t ∈ Finset.range T, firstZeroOccupationMass law w x i t) ≤
      ((n : Real) / law.oneBitMass) *
        (∑ s ∈ Finset.range T, firstZeroEntryMass law w x i s) := by
  classical
  let a : Nat → Real := firstZeroOccupationMass law w x i
  let e : Nat → Real := firstZeroEntryMass law w x i
  let q : Real := law.maskEventMass (lowestMaskEvent i)
  let r : Real := 1 - q
  have hn : 0 < (n : Real) := by
    have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    exact_mod_cast hnNat
  have hscale : 0 ≤ (n : Real) / law.oneBitMass :=
    le_of_lt (div_pos hn hp1)
  have hq : law.oneBitMass / (n : Real) ≤ q :=
    law.lowestMaskEvent_mass_ge_oneBit_per_coordinate i
  have hqle : q ≤ 1 := by
    change law.maskEventMass (lowestMaskEvent i) ≤ 1
    calc
      law.maskEventMass (lowestMaskEvent i) ≤
          ∑ mask : MutationMask n, law.weight mask := by
            unfold maskEventMass
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ (lowestMaskEvent i))
            intro mask _ _
            exact law.weight_nonneg mask
      _ = 1 := law.weight_sum
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  have hmnonneg : ∀ t : Nat, ∀ z : BitString n,
      0 ≤ firstZeroStateMass law w x t z := by
    intro t
    induction t with
    | zero =>
        intro z
        by_cases hz : z = x <;> simp [firstZeroStateMass, hz]
    | succ t ih =>
        intro z
        change 0 ≤ ∑ y : BitString n,
          firstZeroStateMass law w x t y *
            (law.transition (linearFitness w)) y z
        exact Finset.sum_nonneg (fun y _ => mul_nonneg (ih y) (hP.1 y z))
  have hanonneg (t : Nat) : 0 ≤ a t := by
    change 0 ≤ finiteEventMass (firstZeroStateMass law w x t)
      (fun z : BitString n => z ∈ firstZeroLevel i)
    unfold finiteEventMass
    apply Finset.sum_nonneg
    intro z _
    by_cases hz : z ∈ firstZeroLevel i
    · have hmem : z ∈
          ({y : BitString n | y ∈ firstZeroLevel i} : Set (BitString n)) := hz
      rw [Set.indicator_of_mem hmem]
      exact hmnonneg t z
    · have hnot : z ∉
          ({y : BitString n | y ∈ firstZeroLevel i} : Set (BitString n)) := hz
      rw [Set.indicator_of_notMem hnot]
  have hzero : a 0 = e 0 := by
    change (∑ z : BitString n,
        if z ∈ firstZeroLevel i then (if z = x then (1 : Real) else 0) else 0) =
      if x ∈ firstZeroLevel i then (1 : Real) else 0
    calc
      (∑ z : BitString n,
          if z ∈ firstZeroLevel i then (if z = x then (1 : Real) else 0) else 0) =
        ∑ z : BitString n,
          if z = x then (if x ∈ firstZeroLevel i then (1 : Real) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z = x
          · subst z
            simp
          · simp [hz]
      _ = if x ∈ firstZeroLevel i then 1 else 0 := by simp
  have hstep (t : Nat) : a (t + 1) = e (t + 1) + r * a t :=
    firstZeroOccupationMass_succ_eq_entry_add_stay law w hw x i t
  have hsum (t : Nat) :
      q * (∑ s ∈ Finset.range (t + 1), a s) + r * a t =
        ∑ s ∈ Finset.range (t + 1), e s := by
    induction t with
    | zero =>
        have hbase : q * a 0 + r * a 0 = e 0 := by
          rw [← hzero]
          dsimp [r]
          ring
        simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
          zero_add] using hbase
    | succ t ih =>
        have ht := hstep t
        calc
          q * (∑ s ∈ Finset.range ((t + 1) + 1), a s) +
              r * a (t + 1) =
            q * ((∑ s ∈ Finset.range (t + 1), a s) + a (t + 1)) +
              r * a (t + 1) := by rw [Finset.sum_range_succ]
          _ = (q * (∑ s ∈ Finset.range (t + 1), a s) + r * a t) +
              (a (t + 1) - r * a t) := by
                dsimp [r]
                ring
          _ = (∑ s ∈ Finset.range (t + 1), e s) + e (t + 1) := by
                rw [ih, ht]
                ring
          _ = ∑ s ∈ Finset.range ((t + 1) + 1), e s := by
                symm
                rw [Finset.sum_range_succ]
  cases T with
  | zero => simp
  | succ t =>
      have hocc : 0 ≤ ∑ s ∈ Finset.range (t + 1), a s :=
        Finset.sum_nonneg (fun s _ => hanonneg s)
      have hbudget : q * (∑ s ∈ Finset.range (t + 1), a s) ≤
          ∑ s ∈ Finset.range (t + 1), e s := by
        have hsur := hsum t
        nlinarith [mul_nonneg hr (hanonneg t)]
      have hbase : (law.oneBitMass / (n : Real)) *
          (∑ s ∈ Finset.range (t + 1), a s) ≤
            ∑ s ∈ Finset.range (t + 1), e s :=
        (mul_le_mul_of_nonneg_right hq hocc).trans hbudget
      have hid : ((n : Real) / law.oneBitMass) *
          (law.oneBitMass / (n : Real)) = 1 := by
        have hp10 : law.oneBitMass ≠ 0 := ne_of_gt hp1
        have hn0 : (n : Real) ≠ 0 := ne_of_gt hn
        field_simp [hp10, hn0]
      have hscaled := mul_le_mul_of_nonneg_left hbase hscale
      change (∑ s ∈ Finset.range (t + 1), a s) ≤
        ((n : Real) / law.oneBitMass) *
          (∑ s ∈ Finset.range (t + 1), e s)
      calc
        (∑ s ∈ Finset.range (t + 1), a s) =
          ((n : Real) / law.oneBitMass) *
            ((law.oneBitMass / (n : Real)) *
              (∑ s ∈ Finset.range (t + 1), a s)) := by
                rw [← mul_assoc, hid, one_mul]
        _ ≤ _ := hscaled

end OccupationDecidability
end StaticUnaryUnbiasedMutation
end ECRuntime
