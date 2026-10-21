import ECRuntime.StaticUnaryUnbiasedShortPivotPairBudget
import ECRuntime.StaticUnaryUnbiasedLinearLossDecomposition
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 95 statement proposal: recover accepted zero-to-one gains

Stage 94 bounds the one-to-zero loss in accepted, short-radius, non-singleton
pivot events. That *loss-only* bound can be too pessimistic: the same accepted
mask also flips at least its improving pivot from zero to one. This module
proposes retaining the corresponding, original-law gain rather than dropping
it. The gain and loss terms must use exactly the same accepted mask event.

The nine theorem statements were approved by the user after successful
Stage 95 candidate elaboration, and their proof bodies are now drafted.
This focused proof candidate has not yet been compiled by the pinned Lean
toolchain. Keep it outside `ECRuntime.lean` until focused verification and
subsequent regression integration.
No conditional mutation law, independence assumption, or higher moment
assumption is introduced. The last estimate may still be negative; it is
NOT the sharp bounded-first-moment runtime theorem.
-/

/-- The unnormalized, acceptance-event-restricted expected gain from
zero-to-one flips, computed using the *original* mask law. -/
noncomputable def acceptedEventFlippedZeroGain {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ event,
    law.weight mask * (∑ j ∈ zeroToOneFlips x mask, g j)

/-- Exact finite Fubini identity: accepted zero-to-one gain is the sum of
coordinate weights times the original-law mass of their event slices. -/
theorem acceptedEventFlippedZeroGain_eq_coordinateSlices {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) :
    law.acceptedEventFlippedZeroGain event g x =
      ∑ j ∈ zeroPositions x,
        g j * law.maskEventMass (secondCoordinateSlice event j) := by
  classical
  have hpoint (mask : MutationMask n) :
      law.weight mask * (∑ j ∈ zeroToOneFlips x mask, g j) =
        ∑ j ∈ zeroPositions x,
          if j ∈ mask then law.weight mask * g j else 0 := by
    rw [Finset.mul_sum]
    simp only [zeroToOneFlips, zeroPositions, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hm : j ∈ mask <;>
      by_cases hx : x j = false <;> simp_all
  have hslice (j : Fin n) :
      (∑ mask ∈ event,
          if j ∈ mask then law.weight mask * g j else 0) =
        g j * law.maskEventMass (secondCoordinateSlice event j) := by
    unfold maskEventMass secondCoordinateSlice
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mask _
    by_cases hj : j ∈ mask
    · simp [hj, mul_comm]
    · simp [hj]
  unfold acceptedEventFlippedZeroGain
  calc
    (∑ mask ∈ event,
        law.weight mask * (∑ j ∈ zeroToOneFlips x mask, g j)) =
        ∑ mask ∈ event, ∑ j ∈ zeroPositions x,
          if j ∈ mask then law.weight mask * g j else 0 := by
      apply Finset.sum_congr rfl
      intro mask _
      exact hpoint mask
    _ = ∑ j ∈ zeroPositions x, ∑ mask ∈ event,
          if j ∈ mask then law.weight mask * g j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ zeroPositions x,
          g j * law.maskEventMass (secondCoordinateSlice event j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hslice j

/-- With nonnegative potential coefficients, the event-restricted expected
zero-to-one gain cannot be negative. -/
theorem acceptedEventFlippedZeroGain_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n)
    (hg : ∀ j, 0 ≤ g j) :
    0 ≤ law.acceptedEventFlippedZeroGain event g x := by
  unfold acceptedEventFlippedZeroGain
  apply Finset.sum_nonneg
  intro mask hm
  exact mul_nonneg (law.weight_nonneg mask) (by
    apply Finset.sum_nonneg
    intro j hj
    exact hg j)

/-- On an entirely accepted event, the signed selected-potential change is
EXACTLY the accepted zero-to-one gain minus the accepted one-to-zero loss.
The same event occurs in all three terms; no sign assumption is required. -/
theorem acceptedEventWeightedPotentialDrop_eq_zeroGain_sub_oneLoss_of_accepts
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    law.acceptedEventWeightedPotentialDrop event w g x =
      law.acceptedEventFlippedZeroGain event g x -
        law.acceptedEventFlippedOneLoss event g x := by
  classical
  unfold acceptedEventWeightedPotentialDrop acceptedEventFlippedZeroGain
    acceptedEventFlippedOneLoss
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mask hm
  rw [linearErrorPotential_selected_drop_of_accepts
    w g x mask (hacc mask hm), flipContribution_sum_eq_flip_sums]
  ring

/-- Every mask in an accepted short-pivot remainder flips the pivot from
zero to one. Nonnegative other gains therefore leave at least the pivot
coefficient times the ORIGINAL event mass. -/
theorem shortPivotRemainderEvent_zeroGain_ge_pivotMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (hi : x i = false)
    (hg : ∀ j, 0 ≤ g j) :
    g i * law.maskEventMass (shortPivotRemainderEvent w x b i) ≤
      law.acceptedEventFlippedZeroGain
        (shortPivotRemainderEvent w x b i) g x := by
  classical
  unfold acceptedEventFlippedZeroGain maskEventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mask hm
  have hrest : mask ∈ shortAcceptedPivotEvent w x b i :=
    (Finset.mem_erase.mp hm).2
  have hpivot : mask ∈ acceptedLeftmostZeroEvent w x i := by
    unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent at hrest
    exact (Finset.mem_filter.mp hrest).2
  have him : i ∈ mask :=
    acceptedLeftmostZeroEvent_supports_pivot w x i mask hpivot
  have hflip : i ∈ zeroToOneFlips x mask :=
    (mem_zeroToOneFlips x mask i).2 ⟨him, hi⟩
  have hgain : g i ≤ ∑ j ∈ zeroToOneFlips x mask, g j :=
    Finset.single_le_sum (fun j _ => hg j) hflip
  have hmul := mul_le_mul_of_nonneg_left hgain (law.weight_nonneg mask)
  simpa only [mul_comm] using hmul

/-- Recover the pivot's accepted gain before debiting the actual accepted
one-to-zero loss, in each non-singleton short-radius pivot event. -/
theorem shortPivotRemainderEvent_drop_ge_pivotMass_sub_oneLoss {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (hi : x i = false)
    (hg : ∀ j, 0 ≤ g j) :
    g i * law.maskEventMass (shortPivotRemainderEvent w x b i) -
      law.acceptedEventFlippedOneLoss
        (shortPivotRemainderEvent w x b i) g x ≤
      law.acceptedEventWeightedPotentialDrop
        (shortPivotRemainderEvent w x b i) w g x := by
  have hacc : ∀ mask ∈ shortPivotRemainderEvent w x b i,
      Accepts (linearFitness w) x (mutateWithMask x mask) := by
    intro mask hm
    exact shortPivotRemainderEvent_accepts w x b i mask hm
  have hexact := law.acceptedEventWeightedPotentialDrop_eq_zeroGain_sub_oneLoss_of_accepts
    (shortPivotRemainderEvent w x b i) w g x hacc
  have hgain := law.shortPivotRemainderEvent_zeroGain_ge_pivotMass
    w g x b i hi hg
  linarith

/-- Stage 93's short-pivot partition, refined to an exact gain-minus-loss
identity for every non-singleton accepted pivot remainder. -/
theorem acceptedEventWeightedPotentialDrop_short_eq_singleton_add_gains_sub_losses
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b) :
    law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x =
      (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) +
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedZeroGain
            (shortPivotRemainderEvent w x b i) g x) -
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedOneLoss
            (shortPivotRemainderEvent w x b i) g x) := by
  have hsplit := law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_remainders
    hn w g hw x b hb
  have hremainder :
      (∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (shortPivotRemainderEvent w x b i) w g x) =
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedZeroGain
          (shortPivotRemainderEvent w x b i) g x) -
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) g x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact law.acceptedEventWeightedPotentialDrop_eq_zeroGain_sub_oneLoss_of_accepts
      (shortPivotRemainderEvent w x b i) w g x
      (fun mask hm => shortPivotRemainderEvent_accepts w x b i mask hm)
  rw [hsplit, hremainder]
  ring

/-- The singleton gain is supplemented by the guaranteed pivot gain of
accepted non-singleton masks, while their actual losses are retained. -/
theorem acceptedEventWeightedPotentialDrop_short_ge_singleton_add_pivotMass_sub_losses
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (hg : ∀ j, 0 ≤ g j) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) +
        (∑ i ∈ zeroPositions x,
          g i * law.maskEventMass (shortPivotRemainderEvent w x b i)) -
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedOneLoss
            (shortPivotRemainderEvent w x b i) g x) ≤
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x := by
  have hexact := law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_gains_sub_losses
    hn w g hw x b hb
  have hgain :
      (∑ i ∈ zeroPositions x,
        g i * law.maskEventMass (shortPivotRemainderEvent w x b i)) ≤
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedZeroGain
          (shortPivotRemainderEvent w x b i) g x) := by
    apply Finset.sum_le_sum
    intro i hi
    exact law.shortPivotRemainderEvent_zeroGain_ge_pivotMass
      w g x b i ((mem_zeroPositions x i).1 hi) hg
  linarith

/-- Global kernel drift retains the pivot gain of accepted short-radius
non-singleton masks and charges only their actual losses plus the Stage 92
tail first-moment penalty. -/
theorem linearErrorPotential_drift_ge_singleton_add_pivotMass_sub_losses_sub_tailMeanRadius
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (hg : ∀ j, 0 ≤ g j) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) +
        (∑ i ∈ zeroPositions x,
          g i * law.maskEventMass (shortPivotRemainderEvent w x b i)) -
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedOneLoss
            (shortPivotRemainderEvent w x b i) g x) -
        (law.tailMeanRadius b / (n : ℝ)) *
          (∑ j ∈ onePositions x, g j) ≤
      driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x := by
  have hshort := law.acceptedEventWeightedPotentialDrop_short_ge_singleton_add_pivotMass_sub_losses
    hn w g hw x b hb hg
  have htail := law.linearErrorPotential_drift_ge_short_sub_tailMeanRadius
    hn w g x b hg
  linarith

/-- Combine the retained accepted pivot gains with Stage 94's unconditioned
truncated pair-moment loss budget. This is a better envelope than the
loss-only estimate, but need not be positive. -/
theorem linearErrorPotential_drift_ge_singleton_add_pivotMass_sub_pairBudget_sub_tailMeanRadius
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (hg : ∀ j, 0 ≤ g j) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) +
        (∑ i ∈ zeroPositions x,
          g i * law.maskEventMass (shortPivotRemainderEvent w x b i)) -
        (∑ _i ∈ zeroPositions x,
          (law.truncatedSecondFactorialRadiusMoment (b - 1) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
            (∑ j ∈ onePositions x, g j)) -
        (law.tailMeanRadius b / (n : ℝ)) *
          (∑ j ∈ onePositions x, g j) ≤
      driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x := by
  have hpos : 0 < n := by omega
  have hbase := law.linearErrorPotential_drift_ge_singleton_add_pivotMass_sub_losses_sub_tailMeanRadius
    hpos w g hw x b hb hg
  have hbudget :
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) g x) ≤
      (∑ _i ∈ zeroPositions x,
        (law.truncatedSecondFactorialRadiusMoment (b - 1) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
          (∑ j ∈ onePositions x, g j)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact law.shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
      hn w g x b i ((mem_zeroPositions x i).1 hi) hg
  linarith

end StaticUnaryUnbiasedMutation
end ECRuntime
