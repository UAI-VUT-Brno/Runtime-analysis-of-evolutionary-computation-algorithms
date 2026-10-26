import ECRuntime.StaticUnaryUnbiasedLowestMaskBinVal
import ECRuntime.StaticUnaryUnbiasedHighestMaskPivot
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 100: exact excess-radius accounting and signed BinVal drift budgets

The nine theorem propositions were approved after a successful candidate
elaboration round. Their proof bodies are now strict-verification candidates,
not compiler-certified results. The module remains outside the root import
graph pending a clean focused build and later integration.

The original mask law is used throughout. No conditional radius
independence or bounded second moment is assumed. The final bound can be
negative and is NOT the Doerr--Janett--Lengler runtime theorem.
-/

/-- Total original-law radius charge EXCLUDING the unique minimum pivot.
Every nonempty mask contributes exactly `card mask - 1`. -/
noncomputable def lowestPivotExcessRadiusCharge {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) : Real :=
  (lowestMaskEvent i).sum (fun mask =>
    (((mask.card - 1 : Nat) : Real)) * law.weight mask)

/-- Original-law tail-potential charge of less-important flipped coordinates.
The pivot is removed before summing coefficients. -/
noncomputable def lowestPivotWeightedTailCharge {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (g : Fin n → Real)
    (i : Fin n) : Real :=
  (lowestMaskEvent i).sum (fun mask =>
    law.weight mask * (∑ j ∈ mask.erase i, g j))

/-- The non-pivot flip count is exactly `card mask - 1` in a minimum-pivot
class, including singleton masks. -/
theorem lowestMaskEvent_erase_card {n : Nat} (i : Fin n)
    (mask : MutationMask n) (hm : mask ∈ lowestMaskEvent i) :
    (mask.erase i).card = mask.card - 1 := by
  exact Finset.card_erase_of_mem (lowestMaskEvent_supports_pivot i mask hm)

/-- Exact total excess-radius identity, including zero-radius masks and
`n = 0`. The nonempty-mask probability is never conditioned upon. -/
theorem sum_lowestPivotExcessRadiusCharge_add_nonempty_eq_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) :
    (∑ i : Fin n, law.lowestPivotExcessRadiusCharge i) +
      law.maskEventMass
        ((Finset.univ : Finset (MutationMask n)).erase (∅ : MutationMask n)) =
      law.meanRadius := by
  classical
  have hmass :
      (∑ i : Fin n, law.maskEventMass (lowestMaskEvent i)) =
        law.maskEventMass
          ((Finset.univ : Finset (MutationMask n)).erase (∅ : MutationMask n)) := by
    have hpart := lowestMaskEvent_partition_sum (n := n) law.weight
    unfold maskEventMass
    calc
      (∑ i : Fin n, ∑ mask ∈ lowestMaskEvent i, law.weight mask) =
          ∑ mask : MutationMask n,
            if mask = (∅ : MutationMask n) then 0 else law.weight mask := hpart
      _ = ∑ mask : MutationMask n,
          if mask ∈ (Finset.univ : Finset (MutationMask n)).erase ∅
            then law.weight mask else 0 := by
          apply Finset.sum_congr rfl
          intro mask _
          by_cases he : mask = (∅ : MutationMask n)
          · subst mask
            simp
          · simp [he]
      _ = ∑ mask ∈ (Finset.univ : Finset (MutationMask n)).erase ∅,
          law.weight mask :=
            Finset.sum_ite_mem_eq _ _
  have hper (i : Fin n) :
      law.lowestPivotExcessRadiusCharge i +
        law.maskEventMass (lowestMaskEvent i) =
        (lowestMaskEvent i).sum (fun mask =>
          (mask.card : Real) * law.weight mask) := by
    unfold lowestPivotExcessRadiusCharge maskEventMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro mask hm
    have him : i ∈ mask := lowestMaskEvent_supports_pivot i mask hm
    have hcpos : 0 < mask.card := Finset.card_pos.mpr ⟨i, him⟩
    have hc : mask.card - 1 + 1 = mask.card := by omega
    have hcast : (((mask.card - 1 : Nat) : Real) + 1) =
        (mask.card : Real) := by exact_mod_cast hc
    calc
      (((mask.card - 1 : Nat) : Real) * law.weight mask) +
          law.weight mask =
          ((((mask.card - 1 : Nat) : Real) + 1) * law.weight mask) := by ring
      _ = (mask.card : Real) * law.weight mask := by rw [hcast]
  calc
    (∑ i : Fin n, law.lowestPivotExcessRadiusCharge i) +
        law.maskEventMass
          ((Finset.univ : Finset (MutationMask n)).erase (∅ : MutationMask n)) =
        (∑ i : Fin n, law.lowestPivotExcessRadiusCharge i) +
          (∑ i : Fin n, law.maskEventMass (lowestMaskEvent i)) := by
          rw [← hmass]
    _ = ∑ i : Fin n,
          (law.lowestPivotExcessRadiusCharge i +
            law.maskEventMass (lowestMaskEvent i)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin n, ∑ mask ∈ lowestMaskEvent i,
          (mask.card : Real) * law.weight mask := by
          apply Finset.sum_congr rfl
          intro i _
          exact hper i
    _ = law.meanRadius := law.sum_lowestMaskEvent_radius_charge_eq_meanRadius

/-- Each minimum-pivot excess-radius charge is nonnegative. -/
theorem lowestPivotExcessRadiusCharge_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) :
    0 ≤ law.lowestPivotExcessRadiusCharge i := by
  unfold lowestPivotExcessRadiusCharge
  apply Finset.sum_nonneg
  intro mask hm
  exact mul_nonneg (Nat.cast_nonneg _) (law.weight_nonneg mask)

/-- The total charge of all non-pivot flips is controlled by the FIRST
radius moment alone; no second factorial moment is present. -/
theorem sum_lowestPivotExcessRadiusCharge_le_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) :
    (∑ i : Fin n, law.lowestPivotExcessRadiusCharge i) ≤
      law.meanRadius := by
  have hsum := law.sum_lowestPivotExcessRadiusCharge_add_nonempty_eq_meanRadius
  have hmass := law.maskEventMass_nonneg
    ((Finset.univ : Finset (MutationMask n)).erase (∅ : MutationMask n))
  linarith

/-- Weighted charges remain nonnegative for nonnegative potential weights. -/
theorem lowestPivotWeightedTailCharge_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (g : Fin n → Real)
    (hg : ∀ j, 0 ≤ g j) (i : Fin n) :
    0 ≤ law.lowestPivotWeightedTailCharge g i := by
  unfold lowestPivotWeightedTailCharge
  apply Finset.sum_nonneg
  intro mask hm
  exact mul_nonneg (law.weight_nonneg mask) (by
    apply Finset.sum_nonneg
    intro j hj
    exact hg j)

/-- Bounding all potential coefficients by `C` charges each non-pivot bit
at most `C`, without replacing the original distribution by a tilted law. -/
theorem lowestPivotWeightedTailCharge_le_cap {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (g : Fin n → Real)
    (C : Real) (_hC : 0 ≤ C)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ C)
    (i : Fin n) :
    law.lowestPivotWeightedTailCharge g i ≤
      C * law.lowestPivotExcessRadiusCharge i := by
  classical
  have htail (mask : MutationMask n) (hm : mask ∈ lowestMaskEvent i) :
      (∑ j ∈ mask.erase i, g j) ≤
        (((mask.card - 1 : Nat) : Real) * C) := by
    calc
      (∑ j ∈ mask.erase i, g j) ≤
          ∑ _j ∈ mask.erase i, C := by
          apply Finset.sum_le_sum
          intro j hj
          exact (hg j).2
      _ = ((mask.erase i).card : Real) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((mask.card - 1 : Nat) : Real) * C) := by
          rw [lowestMaskEvent_erase_card i mask hm]
  unfold lowestPivotWeightedTailCharge lowestPivotExcessRadiusCharge
  calc
    (∑ mask ∈ lowestMaskEvent i,
        law.weight mask * (∑ j ∈ mask.erase i, g j)) ≤
      ∑ mask ∈ lowestMaskEvent i,
        law.weight mask * (((mask.card - 1 : Nat) : Real) * C) := by
          apply Finset.sum_le_sum
          intro mask hm
          exact mul_le_mul_of_nonneg_left (htail mask hm)
            (law.weight_nonneg mask)
    _ = C * (∑ mask ∈ lowestMaskEvent i,
          (((mask.card - 1 : Nat) : Real)) * law.weight mask) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mask hm
          ring

/-- Global original-law tail-cost bound by `C chi`. This bound can be
quite loose for rare heavy-radius mutations. -/
theorem sum_lowestPivotWeightedTailCharge_le_cap_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (g : Fin n → Real)
    (C : Real) (hC : 0 ≤ C)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ C) :
    (∑ i : Fin n, law.lowestPivotWeightedTailCharge g i) ≤
      C * law.meanRadius := by
  calc
    (∑ i : Fin n, law.lowestPivotWeightedTailCharge g i) ≤
        ∑ i : Fin n, C * law.lowestPivotExcessRadiusCharge i := by
          apply Finset.sum_le_sum
          intro i hi
          exact law.lowestPivotWeightedTailCharge_le_cap g C hC hg i
    _ = C * (∑ i : Fin n, law.lowestPivotExcessRadiusCharge i) := by
          rw [Finset.mul_sum]
    _ ≤ C * law.meanRadius :=
          mul_le_mul_of_nonneg_left
            law.sum_lowestPivotExcessRadiusCharge_le_meanRadius hC

/-- Each accepted BinVal minimum pivot receives full credit `g i`.
Flips at larger numerical indices can cost at most their total `g` weight. -/
theorem acceptedEventWeightedPotentialDrop_lowestPivot_ge_credit_sub_tail {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → Real)
    (hw : SuperincreasingLinearWeights w)
    (hg : ∀ j, 0 ≤ g j)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    g i * law.maskEventMass (lowestMaskEvent i) -
        law.lowestPivotWeightedTailCharge g i ≤
      law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := by
  classical
  have hpoint (mask : MutationMask n) (hm : mask ∈ lowestMaskEvent i) :
      g i - (∑ j ∈ mask.erase i, g j) ≤
        linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask) := by
    have him : i ∈ mask := lowestMaskEvent_supports_pivot i mask hm
    have hacc : Accepts (linearFitness w) x (mutateWithMask x mask) :=
      (superincreasing_accepts_iff_lowest_pivot_zero w hw x i mask hm).2 hi
    have hpivot : i ∈ zeroToOneFlips x mask :=
      (mem_zeroToOneFlips x mask i).2 ⟨him, hi⟩
    have hgain : g i ≤ ∑ j ∈ zeroToOneFlips x mask, g j :=
      Finset.single_le_sum (fun j _ => hg j) hpivot
    have hsub : oneToZeroFlips x mask ⊆ mask.erase i := by
      intro j hj
      obtain ⟨hjm, hjone⟩ := (mem_oneToZeroFlips x mask j).mp hj
      have hji : j ≠ i := by
        intro heq
        subst j
        simp [hi] at hjone
      exact Finset.mem_erase.mpr ⟨hji, hjm⟩
    have hloss :
        (∑ j ∈ oneToZeroFlips x mask, g j) ≤
          (∑ j ∈ mask.erase i, g j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j hj hn
      exact hg j
    have hdrop := linearErrorPotential_selected_drop_of_accepts
      w g x mask hacc
    rw [flipContribution_sum_eq_flip_sums] at hdrop
    linarith
  have hweighted :
      (∑ mask ∈ lowestMaskEvent i,
        law.weight mask * (g i - (∑ j ∈ mask.erase i, g j))) ≤
      law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := by
    unfold acceptedEventWeightedPotentialDrop
    apply Finset.sum_le_sum
    intro mask hm
    exact mul_le_mul_of_nonneg_left (hpoint mask hm)
      (law.weight_nonneg mask)
  have hrearrange :
      g i * law.maskEventMass (lowestMaskEvent i) -
        law.lowestPivotWeightedTailCharge g i =
        (∑ mask ∈ lowestMaskEvent i,
          law.weight mask * (g i - (∑ j ∈ mask.erase i, g j))) := by
    unfold maskEventMass lowestPivotWeightedTailCharge
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro mask hm
    ring
  calc
    g i * law.maskEventMass (lowestMaskEvent i) -
        law.lowestPivotWeightedTailCharge g i =
        (∑ mask ∈ lowestMaskEvent i,
          law.weight mask * (g i - (∑ j ∈ mask.erase i, g j))) := hrearrange
    _ ≤ law.acceptedEventWeightedPotentialDrop
      (lowestMaskEvent i) w g x := hweighted

/-- Explicit one-step BinVal signed drift lower bound under a FIRST-moment
radius assumption. This expression need not be positive near the optimum.
It is an intermediate inequality, NOT a sharp runtime certificate. -/
theorem acceptedEventWeightedPotentialDrop_ge_pivotCredit_sub_cap_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → Real)
    (hw : SuperincreasingLinearWeights w)
    (C : Real) (hC : 0 ≤ C)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ C)
    (x : BitString n) :
    (∑ i ∈ zeroPositions x,
      g i * law.maskEventMass (lowestMaskEvent i)) - C * law.meanRadius ≤
      law.acceptedEventWeightedPotentialDrop
        (Finset.univ : Finset (MutationMask n)) w g x := by
  classical
  have hnonneg : ∀ j, 0 ≤ g j := fun j => (hg j).1
  have htail :
      (∑ i ∈ zeroPositions x, law.lowestPivotWeightedTailCharge g i) ≤
        C * law.meanRadius := by
    calc
      (∑ i ∈ zeroPositions x, law.lowestPivotWeightedTailCharge g i) ≤
          ∑ i : Fin n, law.lowestPivotWeightedTailCharge g i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ (zeroPositions x))
            intro i hm hn
            exact law.lowestPivotWeightedTailCharge_nonneg g hnonneg i
      _ ≤ C * law.meanRadius :=
            law.sum_lowestPivotWeightedTailCharge_le_cap_meanRadius g C hC hg
  have hper :
      (∑ i ∈ zeroPositions x,
        (g i * law.maskEventMass (lowestMaskEvent i) -
          law.lowestPivotWeightedTailCharge g i)) ≤
        ∑ i ∈ zeroPositions x,
          law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x := by
    apply Finset.sum_le_sum
    intro i hm
    exact law.acceptedEventWeightedPotentialDrop_lowestPivot_ge_credit_sub_tail
      w g hw hnonneg x i ((mem_zeroPositions x i).mp hm)
  calc
    (∑ i ∈ zeroPositions x,
        g i * law.maskEventMass (lowestMaskEvent i)) - C * law.meanRadius ≤
      (∑ i ∈ zeroPositions x,
        g i * law.maskEventMass (lowestMaskEvent i)) -
        (∑ i ∈ zeroPositions x, law.lowestPivotWeightedTailCharge g i) := by
          linarith
    _ = (∑ i ∈ zeroPositions x,
        (g i * law.maskEventMass (lowestMaskEvent i) -
          law.lowestPivotWeightedTailCharge g i)) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ (∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop (lowestMaskEvent i) w g x) := hper
    _ = law.acceptedEventWeightedPotentialDrop
          (Finset.univ : Finset (MutationMask n)) w g x :=
            (law.acceptedEventWeightedPotentialDrop_eq_sum_lowest_zeros
              w g hw x).symm

end StaticUnaryUnbiasedMutation
end ECRuntime
