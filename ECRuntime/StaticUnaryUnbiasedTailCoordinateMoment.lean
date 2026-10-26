import ECRuntime.StaticUnaryUnbiasedCoordinateTailLoss
import ECRuntime.StaticUnaryUnbiasedAcceptedRadiusTail
import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 92: tail-first-moment coordinate marginals and signed drift

Exchangeability is used only for the unconditional high-radius mask law.
Acceptance remains a finite-event restriction.  In positive dimension, the
probability that coordinate `j` flips in a mutation of radius at least `b` is
exactly `E[K * 1_{K ≥ b}] / n`.  The resulting signed-tail drift penalty
charges currently-one potential coefficients at this rate.

A bounded first moment does not force this truncated mean to tend to zero
uniformly over dimension-dependent radius distributions.  Likewise, the
short-radius contribution is not assumed nonnegative.  The last theorem
identifies an explicit *additional* short-radius condition for positivity,
not a proof of the full mean-only sharp upper runtime theorem.
-/

/-- The unconditional first radius moment restricted to `K ≥ b`. -/
noncomputable def tailMeanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) : ℝ :=
  ∑ mask : MutationMask n,
    if b ≤ mask.card then (mask.card : ℝ) * law.weight mask else 0

/-- Mass of masks which have radius at least `b` and flip coordinate `j`. -/
noncomputable def highRadiusCoordinateFlipMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) (j : Fin n) : ℝ :=
  ∑ mask : MutationMask n,
    if b ≤ mask.card ∧ j ∈ mask then law.weight mask else 0

/-- The tail first moment agrees exactly with the derived radius law. -/
theorem tailMeanRadius_eq_radius_sum {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) :
    law.tailMeanRadius b =
      ∑ k ∈ Finset.range (n + 1),
        if b ≤ k then (k : ℝ) * law.radiusMass k else 0 := by
  classical
  unfold tailMeanRadius
  calc
    (∑ mask : MutationMask n,
      if b ≤ mask.card then (mask.card : ℝ) * law.weight mask else 0) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            if b ≤ mask.card then (mask.card : ℝ) * law.weight mask else 0 := by
        simpa using (Finset.sum_powerset (Finset.univ : Finset (Fin n))
          (fun mask : MutationMask n =>
            if b ≤ mask.card then (mask.card : ℝ) * law.weight mask else 0))
    _ = ∑ k ∈ Finset.range (n + 1),
          if b ≤ k then (k : ℝ) * law.radiusMass k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hbk : b ≤ k
      · rw [if_pos hbk]
        unfold radiusMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mask hm
        have hcard : mask.card = k := (Finset.mem_powersetCard.mp hm).2
        simp only [hcard, if_pos hbk]
      · rw [if_neg hbk]
        apply Finset.sum_eq_zero
        intro mask hm
        have hcard : mask.card = k := (Finset.mem_powersetCard.mp hm).2
        simp only [hcard, if_neg hbk]

/-- The tail first moment is nonnegative. -/
theorem tailMeanRadius_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) :
    0 ≤ law.tailMeanRadius b := by
  unfold tailMeanRadius
  apply Finset.sum_nonneg
  intro mask hm
  by_cases hb : b ≤ mask.card
  · simp only [if_pos hb]
    exact mul_nonneg (Nat.cast_nonneg _) (law.weight_nonneg mask)
  · simp only [if_neg hb]
    exact le_refl 0

/-- The restricted first moment is at most the unconditional first moment. -/
theorem tailMeanRadius_le_meanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) :
    law.tailMeanRadius b ≤ law.meanRadius := by
  rw [law.meanRadius_eq_sum_mask_card_weight]
  unfold tailMeanRadius
  apply Finset.sum_le_sum
  intro mask hm
  by_cases hb : b ≤ mask.card
  · simpa only [if_pos hb] using
      (le_refl ((mask.card : ℝ) * law.weight mask))
  · simp only [if_neg hb]
    exact mul_nonneg (Nat.cast_nonneg _) (law.weight_nonneg mask)

/-- Unary unbiasedness still makes the high-radius flip mass exchangeable. -/
theorem highRadiusCoordinateFlipMass_eq {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) (i j : Fin n) :
    law.highRadiusCoordinateFlipMass b i =
      law.highRadiusCoordinateFlipMass b j := by
  classical
  unfold highRadiusCoordinateFlipMass
  let e : MutationMask n ≃ MutationMask n := swapMaskEquiv i j
  refine Fintype.sum_equiv e
    (fun mask : MutationMask n =>
      if b ≤ mask.card ∧ i ∈ mask then law.weight mask else 0)
    (fun mask : MutationMask n =>
      if b ≤ mask.card ∧ j ∈ mask then law.weight mask else 0) ?_
  intro mask
  have hcard : mask.card = (e mask).card := by simp [e]
  have hw : law.weight mask = law.weight (e mask) :=
    law.card_invariant hcard
  have hmem : j ∈ e mask ↔ i ∈ mask := by simp [e]
  have hrad : b ≤ mask.card ↔ b ≤ (e mask).card := by rw [hcard]
  by_cases h : b ≤ mask.card ∧ i ∈ mask
  · have he : b ≤ (e mask).card ∧ j ∈ e mask :=
      And.intro (hrad.mp h.1) (hmem.mpr h.2)
    simp only [if_pos h, if_pos he]
    exact hw
  · have he : Not (b ≤ (e mask).card ∧ j ∈ e mask) := by
      intro he
      exact h (And.intro (hrad.mpr he.1) (hmem.mp he.2))
    simp only [if_neg h, if_neg he]

/-- Finite double counting: summing the tail coordinate marginals gives
precisely the radius-tail first moment. -/
theorem sum_highRadiusCoordinateFlipMass_eq_tailMeanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) :
    (∑ j : Fin n, law.highRadiusCoordinateFlipMass b j) =
      law.tailMeanRadius b := by
  classical
  unfold highRadiusCoordinateFlipMass tailMeanRadius
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mask hm
  by_cases hb : b ≤ mask.card
  · calc
      (∑ j : Fin n,
        if b ≤ mask.card ∧ j ∈ mask then law.weight mask else 0) =
          ∑ j : Fin n, if j ∈ mask then law.weight mask else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hb]
      _ = ∑ j ∈ mask, law.weight mask := by simp
      _ = (mask.card : ℝ) * law.weight mask := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = if b ≤ mask.card then (mask.card : ℝ) * law.weight mask else 0 := by
          simp [hb]
  · simp [hb]

/-- Each specified coordinate carries exactly one n-th of the tail first
moment.  No independence of flips is assumed. -/
theorem highRadiusCoordinateFlipMass_eq_tailMeanRadius_div {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (b : Nat) (j : Fin n) :
    law.highRadiusCoordinateFlipMass b j =
      law.tailMeanRadius b / (n : ℝ) := by
  have hsum := law.sum_highRadiusCoordinateFlipMass_eq_tailMeanRadius b
  have hconst :
      (∑ i : Fin n, law.highRadiusCoordinateFlipMass b i) =
        (n : ℝ) * law.highRadiusCoordinateFlipMass b j := by
    calc
      (∑ i : Fin n, law.highRadiusCoordinateFlipMass b i) =
          ∑ _i : Fin n, law.highRadiusCoordinateFlipMass b j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact law.highRadiusCoordinateFlipMass_eq b i j
      _ = (n : ℝ) * law.highRadiusCoordinateFlipMass b j := by simp
  have hmul :
      (n : ℝ) * law.highRadiusCoordinateFlipMass b j =
        law.tailMeanRadius b := hconst.symm.trans hsum
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  apply (eq_div_iff hn0).2
  simpa [mul_comm] using hmul

/-- The two-filter mask mass is the exact high-radius coordinate marginal. -/
theorem maskEventMass_highRadius_coordinateSlice_eq {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat) (j : Fin n) :
    law.maskEventMass
        (secondCoordinateSlice (highRadiusMaskEvent (n := n) b) j) =
      law.highRadiusCoordinateFlipMass b j := by
  classical
  unfold maskEventMass secondCoordinateSlice highRadiusMaskEvent
    highRadiusCoordinateFlipMass
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hm
  by_cases hb : b ≤ mask.card <;>
    by_cases hj : j ∈ mask <;> simp [hb, hj]

/-- Any event contained in the radius tail has a coordinate slice bounded by
the exact *unconditional* high-radius coordinate mass. -/
theorem maskEventMass_slice_le_highRadiusCoordinateFlipMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (b : Nat)
    (event : Finset (MutationMask n))
    (hsub : event ⊆ highRadiusMaskEvent (n := n) b)
    (j : Fin n) :
    law.maskEventMass (secondCoordinateSlice event j) ≤
      law.highRadiusCoordinateFlipMass b j := by
  rw [← law.maskEventMass_highRadius_coordinateSlice_eq b j]
  apply law.maskEventMass_mono
  intro mask hm
  change mask ∈ event.filter (fun m => j ∈ m) at hm
  change mask ∈ (highRadiusMaskEvent (n := n) b).filter (fun m => j ∈ m)
  exact Finset.mem_filter.mpr
    (And.intro (hsub (Finset.mem_filter.mp hm).1)
      (Finset.mem_filter.mp hm).2)

/-- The accepted high-radius flipped-one loss is bounded by the tail *first*
moment divided by the dimension, times the potential of the one bits. -/
theorem acceptedHighRadiusFlippedOneLoss_le_tailMeanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (x : BitString n) (b : Nat)
    (hg : forall j, 0 ≤ g j) :
    law.acceptedEventFlippedOneLoss
      (acceptedHighRadiusMaskEvent w x b) g x ≤
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) := by
  classical
  rw [law.acceptedEventFlippedOneLoss_eq_coordinateSlices]
  have haccSub : acceptedHighRadiusMaskEvent w x b ⊆
      highRadiusMaskEvent (n := n) b := by
    intro mask hm
    change mask ∈ (highRadiusMaskEvent (n := n) b).filter
      (fun m => Accepts (linearFitness w) x (mutateWithMask x m)) at hm
    exact (Finset.mem_filter.mp hm).1
  calc
    (∑ j ∈ onePositions x,
      g j * law.maskEventMass
        (secondCoordinateSlice (acceptedHighRadiusMaskEvent w x b) j)) ≤
        ∑ j ∈ onePositions x,
          g j * (law.tailMeanRadius b / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hslice := law.maskEventMass_slice_le_highRadiusCoordinateFlipMass
        b (acceptedHighRadiusMaskEvent w x b) haccSub j
      rw [law.highRadiusCoordinateFlipMass_eq_tailMeanRadius_div hn b j] at hslice
      exact mul_le_mul_of_nonneg_left hslice (hg j)
    _ = (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A signed bound for accepted long-radius changes using the restricted
first moment; unlike a probability bound it controls actual potential loss. -/
theorem acceptedHighRadiusPotentialDrop_ge_neg_tailMeanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (x : BitString n) (b : Nat)
    (hg : forall j, 0 ≤ g j) :
    -((law.tailMeanRadius b / (n : ℝ)) *
       (∑ j ∈ onePositions x, g j)) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x := by
  have hloss := law.acceptedHighRadiusPotentialDrop_ge_neg_flippedOneLoss
    w g x b hg
  change -(law.acceptedEventFlippedOneLoss
    (acceptedHighRadiusMaskEvent w x b) g x) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x at hloss
  have htail := law.acceptedHighRadiusFlippedOneLoss_le_tailMeanRadius
    hn w g x b hg
  linarith

/-- The exact short/long signed decomposition yields a global first-tail-
moment lower bound without using a second factorial moment. -/
theorem linearErrorPotential_drift_ge_short_sub_tailMeanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (x : BitString n) (b : Nat)
    (hg : forall j, 0 ≤ g j) :
    driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x ≥
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) := by
  have hglobal :
      law.acceptedEventWeightedPotentialDrop Finset.univ w g x ≥
        law.acceptedEventWeightedPotentialDrop
          (shortRadiusMaskEvent (n := n) b) w g x -
        (law.tailMeanRadius b / (n : ℝ)) *
          (∑ j ∈ onePositions x, g j) := by
    have hsplit := law.acceptedEventWeightedPotentialDrop_univ_eq_shortRadius_add_highRadius
      w g x b
    rw [law.acceptedEventWeightedPotentialDrop_highRadius_eq_acceptedHighRadius
      w g x b] at hsplit
    have htail := law.acceptedHighRadiusPotentialDrop_ge_neg_tailMeanRadius
      hn w g x b hg
    linarith
  rw [law.drift_eq_mask_sum]
  exact hglobal

/-- Quantified conditional singleton-gain comparison: if the entire signed
short-radius drift dominates the exact positive singleton term, the
remaining tail penalty is charged only to currently-one coordinates.
The short-radius hypothesis is **not** inferred from a bounded mean. -/
theorem linearErrorPotential_drift_ge_singleton_sub_tailMeanRadius {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (x : BitString n) (b : Nat)
    (hg : forall j, 0 ≤ g j)
    (hshort :
      (law.oneBitMass / (n : ℝ)) *
          (∑ j ∈ zeroPositions x, g j) ≤
        law.acceptedEventWeightedPotentialDrop
          (shortRadiusMaskEvent (n := n) b) w g x) :
    (law.oneBitMass / (n : ℝ)) *
        (∑ j ∈ zeroPositions x, g j) -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) ≤
      driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x := by
  have hbound := law.linearErrorPotential_drift_ge_short_sub_tailMeanRadius
    hn w g x b hg
  linarith

end StaticUnaryUnbiasedMutation
end ECRuntime
