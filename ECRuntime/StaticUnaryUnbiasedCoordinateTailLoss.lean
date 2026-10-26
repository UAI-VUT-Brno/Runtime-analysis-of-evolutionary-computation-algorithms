import ECRuntime.StaticUnaryUnbiasedAcceptedTailLoss
import ECRuntime.StaticUnaryUnbiasedEventWeightedRightLoss
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 91: coordinate-resolved accepted-tail loss under a bounded first moment

The Stage-90 bound for accepted high-radius mutations charges the entire
potential-coefficient sum against the probability of a high-radius event.
Here each one-to-zero loss is instead charged to its *own* coordinate flip.
The exact finite-Fubini identity retains the acceptance event in every slice.
Unary-unbiased coordinate symmetry then bounds each slice by `chi/n`, giving
an upper loss estimate involving only coefficients at currently-one bits.

This is an unconditional marginal estimate applied to acceptance-restricted
slices; it does not assume that acceptance is independent of coordinate flips.
It also does not prove the full mean-only runtime theorem: the truncated
short-radius drift still needs a suitable lower bound, and an `O(chi/n)`
penalty can remain too large relative to the singleton gain.
-/

/-- The currently-one positions of the parent state. -/
def onePositions {n : ℕ} (x : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = true)

@[simp] theorem mem_onePositions_iff {n : ℕ}
    (x : BitString n) (j : Fin n) :
    j ∈ onePositions x ↔ x j = true := by
  simp [onePositions]

/-- Event-restricted expected loss from one-to-zero coordinate flips.
The event may be arbitrary; in particular it may encode both acceptance and
radius truncation. No probability conditioning is performed. -/
noncomputable def acceptedEventFlippedOneLoss {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ event,
    law.weight mask * (∑ j ∈ oneToZeroFlips x mask, g j)

/-- Exact coordinate-by-coordinate loss accounting. Every term retains the
original accepted-event restriction, rather than replacing it with an
independent-bit model or a conditional mutation law. -/
theorem acceptedEventFlippedOneLoss_eq_coordinateSlices {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) :
    law.acceptedEventFlippedOneLoss event g x =
      ∑ j ∈ onePositions x,
        g j * law.maskEventMass (secondCoordinateSlice event j) := by
  classical
  have hpoint (mask : MutationMask n) :
      law.weight mask * (∑ j ∈ oneToZeroFlips x mask, g j) =
        ∑ j ∈ onePositions x,
          if j ∈ mask then law.weight mask * g j else 0 := by
    rw [Finset.mul_sum]
    simp only [oneToZeroFlips, onePositions, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hm : j ∈ mask <;>
      by_cases hx : x j = true <;> simp_all
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
  unfold acceptedEventFlippedOneLoss
  calc
    (∑ mask ∈ event,
        law.weight mask * (∑ j ∈ oneToZeroFlips x mask, g j)) =
        ∑ mask ∈ event, ∑ j ∈ onePositions x,
          if j ∈ mask then law.weight mask * g j else 0 := by
      apply Finset.sum_congr rfl
      intro mask _
      exact hpoint mask
    _ = ∑ j ∈ onePositions x, ∑ mask ∈ event,
          if j ∈ mask then law.weight mask * g j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ onePositions x,
          g j * law.maskEventMass (secondCoordinateSlice event j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hslice j

/-- Event-restricted flipped-one loss is nonnegative for nonnegative
potential weights, even when the event contains rejected masks. -/
theorem acceptedEventFlippedOneLoss_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n)
    (hg : ∀ j, 0 ≤ g j) :
    0 ≤ law.acceptedEventFlippedOneLoss event g x := by
  unfold acceptedEventFlippedOneLoss
  apply Finset.sum_nonneg
  intro mask hm
  exact mul_nonneg (law.weight_nonneg mask) (by
    apply Finset.sum_nonneg
    intro j hj
    exact hg j)

/-- First-moment coordinate envelope for the event-restricted loss.
Unlike the Stage-90 total-coefficient bound, this is normalized by `n` and
uses only currently-one coordinates. It is uniform over all finite mask
events, including accepted high-radius events. -/
theorem acceptedEventFlippedOneLoss_le_oneMass_mul_meanFlipRate {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n)
    (hg : ∀ j, 0 ≤ g j) :
    law.acceptedEventFlippedOneLoss event g x ≤
      (law.meanRadius / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) := by
  rw [law.acceptedEventFlippedOneLoss_eq_coordinateSlices]
  calc
    (∑ j ∈ onePositions x,
        g j * law.maskEventMass (secondCoordinateSlice event j)) ≤
        ∑ j ∈ onePositions x,
          g j * (law.meanRadius / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hslice :
          law.maskEventMass (secondCoordinateSlice event j) ≤
            law.meanRadius / (n : ℝ) := by
        apply law.maskEventMass_le_meanRadius_div
          (secondCoordinateSlice event j) j
        intro mask hmask
        exact (Finset.mem_filter.mp hmask).2
      exact mul_le_mul_of_nonneg_left hslice (hg j)
    _ = (law.meanRadius / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Accepted high-radius signed drift loses at most `chi/n` times the
potential weight of the currently-one positions. This is a valid *signed*
loss estimate, not merely a high-radius event-probability bound. -/
theorem acceptedHighRadiusPotentialDrop_ge_neg_oneMass_mul_meanFlipRate {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (hg : ∀ j, 0 ≤ g j) :
    -(law.meanRadius / (n : ℝ) *
        (∑ j ∈ onePositions x, g j)) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x := by
  have htail := law.acceptedHighRadiusPotentialDrop_ge_neg_flippedOneLoss
    w g x b hg
  change -(law.acceptedEventFlippedOneLoss
    (acceptedHighRadiusMaskEvent w x b) g x) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x at htail
  have hcoord := law.acceptedEventFlippedOneLoss_le_oneMass_mul_meanFlipRate
    (acceptedHighRadiusMaskEvent w x b) g x hg
  linarith

/-- Recombine the exact short/long signed partition with the coordinate-wise
accepted-tail estimate. No sign is asserted for short-radius drift. -/
theorem acceptedEventWeightedPotentialDrop_univ_ge_short_sub_oneMass_mul_meanFlipRate
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (hg : ∀ j, 0 ≤ g j) :
    law.acceptedEventWeightedPotentialDrop Finset.univ w g x ≥
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x -
      (law.meanRadius / (n : ℝ)) * (∑ j ∈ onePositions x, g j) := by
  have hsplit := law.acceptedEventWeightedPotentialDrop_univ_eq_shortRadius_add_highRadius
    w g x b
  rw [law.acceptedEventWeightedPotentialDrop_highRadius_eq_acceptedHighRadius
    w g x b] at hsplit
  have htail := law.acceptedHighRadiusPotentialDrop_ge_neg_oneMass_mul_meanFlipRate
    w g x b hg
  linarith

/-- Markov-kernel version of the normalized state-dependent signed drift
estimate. The discarded large-radius term is bounded rather than dropped. -/
theorem linearErrorPotential_drift_ge_short_sub_oneMass_mul_meanFlipRate {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n)
    (b : ℕ) (hg : ∀ j, 0 ≤ g j) :
    driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x ≥
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x -
      (law.meanRadius / (n : ℝ)) * (∑ j ∈ onePositions x, g j) := by
  rw [law.drift_eq_mask_sum]
  exact law.acceptedEventWeightedPotentialDrop_univ_ge_short_sub_oneMass_mul_meanFlipRate
    w g x b hg

end StaticUnaryUnbiasedMutation
end ECRuntime
