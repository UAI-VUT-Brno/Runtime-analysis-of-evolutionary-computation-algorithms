import ECRuntime.StaticUnaryUnbiasedAcceptedGainAlignment
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 97 approved proof candidate: coordinatewise residual-loss cancellation

Stage 96 charges the accepted one-to-zero loss using a global upper/lower
coefficient ratio. This proposed continuation keeps the *coordinatewise*
nonnegative excess `g j - scale * w j` and charges only the actual accepted
flips of those residual coefficients. The objective acceptance margin and
residual zero-to-one gains are retained in intermediate exact identities.

All probabilities are computed under the original static mutation law, not
under a law conditioned on acceptance. Only a lower coefficient comparison
is required, not a uniform multiplicative upper bound.

The nine theorem statements were approved after a clean Stage-97-fix-1
candidate elaboration. Their proofs are drafted here, but have NOT yet been
compiled on the pinned Lean toolchain. This standalone module remains outside
the promoted root until focused verification and subsequent regression
integration. The sharp bounded-first-moment runtime upper/lower bounds remain
open.
-/

/-- Excess of potential coefficient above the common objective scale. -/
def residualPotentialWeights {n : ℕ}
    (w g : Fin n → ℝ) (scale : ℝ) : Fin n → ℝ :=
  fun j => g j - scale * w j

/-- A coordinatewise lower comparison implies nonnegative residual weights. -/
theorem residualPotentialWeights_nonneg {n : ℕ}
    (w g : Fin n → ℝ) (scale : ℝ)
    (hres : ∀ j, scale * w j ≤ g j) :
    ∀ j, 0 ≤ residualPotentialWeights w g scale j := by
  intro j
  change 0 ≤ g j - scale * w j
  exact sub_nonneg.mpr (hres j)

/-- Split the original-law accepted zero-to-one gain into the objective-scaled
part and a coordinatewise residual gain. No acceptance premise is needed. -/
theorem acceptedEventFlippedZeroGain_eq_scaled_add_residual {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (scale : ℝ) :
    law.acceptedEventFlippedZeroGain event g x =
      scale * law.acceptedEventFlippedZeroGain event w x +
        law.acceptedEventFlippedZeroGain event
          (residualPotentialWeights w g scale) x := by
  classical
  simp only [law.acceptedEventFlippedZeroGain_eq_coordinateSlices]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [residualPotentialWeights]
  ring

/-- The same unconditioned original-law split for one-to-zero losses. -/
theorem acceptedEventFlippedOneLoss_eq_scaled_add_residual {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (scale : ℝ) :
    law.acceptedEventFlippedOneLoss event g x =
      scale * law.acceptedEventFlippedOneLoss event w x +
        law.acceptedEventFlippedOneLoss event
          (residualPotentialWeights w g scale) x := by
  classical
  simp only [law.acceptedEventFlippedOneLoss_eq_coordinateSlices]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [residualPotentialWeights]
  ring

/-- Accepted potential drop is the scaled objective acceptance margin plus
exactly the gain minus loss of the residual potential. -/
theorem acceptedEventWeightedPotentialDrop_eq_scaledMargin_add_residualDrop
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (scale : ℝ)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    law.acceptedEventWeightedPotentialDrop event w g x =
      scale * (law.acceptedEventFlippedZeroGain event w x -
        law.acceptedEventFlippedOneLoss event w x) +
      (law.acceptedEventFlippedZeroGain event
        (residualPotentialWeights w g scale) x -
       law.acceptedEventFlippedOneLoss event
        (residualPotentialWeights w g scale) x) := by
  rw [law.acceptedEventWeightedPotentialDrop_eq_zeroGain_sub_oneLoss_of_accepts
    event w g x hacc,
    law.acceptedEventFlippedZeroGain_eq_scaled_add_residual event w g x scale,
    law.acceptedEventFlippedOneLoss_eq_scaled_add_residual event w g x scale]
  ring

/-- With nonnegative residual coordinates, dropping ONLY residual positive
gains preserves the nonnegative objective-margin credit. -/
theorem acceptedEventWeightedPotentialDrop_ge_scaledMargin_sub_residualLoss
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (scale : ℝ)
    (hres : ∀ j, scale * w j ≤ g j)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    scale * (law.acceptedEventFlippedZeroGain event w x -
      law.acceptedEventFlippedOneLoss event w x) -
      law.acceptedEventFlippedOneLoss event
        (residualPotentialWeights w g scale) x ≤
    law.acceptedEventWeightedPotentialDrop event w g x := by
  have hr : ∀ j, 0 ≤ residualPotentialWeights w g scale j :=
    residualPotentialWeights_nonneg w g scale hres
  have hgain : 0 ≤ law.acceptedEventFlippedZeroGain event
      (residualPotentialWeights w g scale) x :=
    law.acceptedEventFlippedZeroGain_nonneg event
      (residualPotentialWeights w g scale) x hr
  have hexact :=
    law.acceptedEventWeightedPotentialDrop_eq_scaledMargin_add_residualDrop
      event w g x scale hacc
  linarith

/-- For a nonnegative scale the accepted objective margin itself can be
dropped, charging only accepted residual one-to-zero flips. -/
theorem acceptedEventWeightedPotentialDrop_ge_neg_residualLoss_of_accepts
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (scale : ℝ)
    (hscale : 0 ≤ scale)
    (hres : ∀ j, scale * w j ≤ g j)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    -(law.acceptedEventFlippedOneLoss event
      (residualPotentialWeights w g scale) x) ≤
    law.acceptedEventWeightedPotentialDrop event w g x := by
  have hmargin : 0 ≤ law.acceptedEventFlippedZeroGain event w x -
      law.acceptedEventFlippedOneLoss event w x :=
    sub_nonneg.mpr (law.acceptedEventFlippedZeroGain_ge_oneLoss_of_accepts
      event w x hacc)
  have hscaled : 0 ≤ scale *
      (law.acceptedEventFlippedZeroGain event w x -
        law.acceptedEventFlippedOneLoss event w x) :=
    mul_nonneg hscale hmargin
  have hbound :=
    law.acceptedEventWeightedPotentialDrop_ge_scaledMargin_sub_residualLoss
      event w g x scale hres hacc
  linarith

/-- Accepted short-pivot remainder: the negative contribution is charged
to its actual one-to-zero residual flips, not a global coefficient ratio. -/
theorem shortPivotRemainderEvent_drop_ge_neg_residualLoss
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (scale : ℝ) (hscale : 0 ≤ scale)
    (hres : ∀ j, scale * w j ≤ g j) :
    -(law.acceptedEventFlippedOneLoss
      (shortPivotRemainderEvent w x b i)
      (residualPotentialWeights w g scale) x) ≤
    law.acceptedEventWeightedPotentialDrop
      (shortPivotRemainderEvent w x b i) w g x := by
  exact law.acceptedEventWeightedPotentialDrop_ge_neg_residualLoss_of_accepts
    (shortPivotRemainderEvent w x b i) w g x scale hscale hres
    (fun mask hm => shortPivotRemainderEvent_accepts w x b i mask hm)

/-- The global drift retains Stage 95's singleton mass and Stage 92's
first-moment tail penalty, but uses actual accepted residual losses. -/
theorem linearErrorPotential_drift_ge_singleton_sub_residualLoss_sub_tail
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hres : ∀ j, scale * w j ≤ g j) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) -
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i)
          (residualPotentialWeights w g scale) x) -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) ≤
    driftAt (law.transition (linearFitness w))
      (linearErrorPotential g) x := by
  have hg : ∀ j, 0 ≤ g j := by
    intro j
    have hwj : 0 ≤ w j := (hw j).le
    exact (mul_nonneg hscale hwj).trans (hres j)
  have hsplit := law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_remainders
    hn w g hw x b hb
  have hsum :
      (∑ i ∈ zeroPositions x,
        -(law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i)
          (residualPotentialWeights w g scale) x)) ≤
      (∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (shortPivotRemainderEvent w x b i) w g x) := by
    apply Finset.sum_le_sum
    intro i _
    exact law.shortPivotRemainderEvent_drop_ge_neg_residualLoss
      w g x b i scale hscale hres
  rw [Finset.sum_neg_distrib] at hsum
  have htail := law.linearErrorPotential_drift_ge_short_sub_tailMeanRadius
    hn w g x b hg
  linarith

/-- A fully explicit truncated-pair-moment corollary uses the sum of the
nonnegative residual coefficients *at current one-bits*. This is never worse
than Stage 96's global-distortion pair bound under the same sandwich.
It can still be negative and is not a sharp mean-only runtime theorem. -/
theorem linearErrorPotential_drift_ge_singleton_sub_residualPairBudget_sub_tail
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hres : ∀ j, scale * w j ≤ g j) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) -
      (∑ _i ∈ zeroPositions x,
        (law.truncatedSecondFactorialRadiusMoment (b - 1) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
        (∑ j ∈ onePositions x,
          residualPotentialWeights w g scale j)) -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) ≤
    driftAt (law.transition (linearFitness w))
      (linearErrorPotential g) x := by
  have hpos : 0 < n := by omega
  have hbase := law.linearErrorPotential_drift_ge_singleton_sub_residualLoss_sub_tail
    hpos w g hw x b hb scale hscale hres
  have hr : ∀ j, 0 ≤ residualPotentialWeights w g scale j :=
    residualPotentialWeights_nonneg w g scale hres
  have hbudget :
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i)
          (residualPotentialWeights w g scale) x) ≤
      (∑ _i ∈ zeroPositions x,
        (law.truncatedSecondFactorialRadiusMoment (b - 1) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
          (∑ j ∈ onePositions x,
            residualPotentialWeights w g scale j)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact law.shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
      hn w (residualPotentialWeights w g scale) x b i
      ((mem_zeroPositions x i).1 hi) hr
  linarith

end StaticUnaryUnbiasedMutation
end ECRuntime
