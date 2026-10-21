import ECRuntime.StaticUnaryUnbiasedShortPivotGainRecovery
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 96: acceptance-aware potential/objective alignment

Stage 95 retains the accepted zero-to-one gain alongside the loss. This stage
proposes a *relative-coefficient* certificate that uses objective acceptance
to cancel most of that loss. If `lower * w j <= g j <= upper * w j`
coordinatewise and `0 <= lower`, an accepted mask incurs potential drop at
least `-(upper-lower)` times its *accepted objective-weighted* one-to-zero
loss. No independence or conditioning of the original mask law is used.

The nine theorem statements were approved by the user following successful
candidate-mode elaboration and their proof bodies are now drafted. This module
is not root-imported: strict focused Lean verification on the pinned toolchain
is required before the proofs can be considered certified. The final pair
budget is conservative and may be negative. No sharp bounded-first-moment
runtime bound or matching lower bound is claimed.
-/

/-- Two-sided multiplicative comparison of potential and objective weights.
The two bounds are coordinatewise, not statements about the mutation law. -/
def PotentialWeightSandwich {n : ℕ}
    (w g : Fin n → ℝ) (lower upper : ℝ) : Prop :=
  ∀ j, lower * w j ≤ g j ∧ g j ≤ upper * w j

/-- Event-restricted potential gain dominates the lower-multiple objective gain.
Both sides use exactly the same unconditioned original mask event. -/
theorem acceptedEventFlippedZeroGain_ge_scaledObjectiveGain {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (lower upper : ℝ)
    (hband : PotentialWeightSandwich w g lower upper) :
    lower * law.acceptedEventFlippedZeroGain event w x ≤
      law.acceptedEventFlippedZeroGain event g x := by
  classical
  unfold acceptedEventFlippedZeroGain
  calc
    lower * (∑ mask ∈ event,
        law.weight mask * (∑ j ∈ zeroToOneFlips x mask, w j)) =
        ∑ mask ∈ event,
          law.weight mask * (lower * (∑ j ∈ zeroToOneFlips x mask, w j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ ≤ ∑ mask ∈ event,
          law.weight mask * (∑ j ∈ zeroToOneFlips x mask, g j) := by
      apply Finset.sum_le_sum
      intro mask _
      apply mul_le_mul_of_nonneg_left _ (law.weight_nonneg mask)
      calc
        lower * (∑ j ∈ zeroToOneFlips x mask, w j) =
            ∑ j ∈ zeroToOneFlips x mask, lower * w j := by rw [Finset.mul_sum]
        _ ≤ ∑ j ∈ zeroToOneFlips x mask, g j := by
          apply Finset.sum_le_sum
          intro j _
          exact (hband j).1

/-- Event-restricted potential loss is bounded by the upper-multiple
objective loss, without conditioning the mask law on acceptance. -/
theorem acceptedEventFlippedOneLoss_le_scaledObjectiveLoss {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (lower upper : ℝ)
    (hband : PotentialWeightSandwich w g lower upper) :
    law.acceptedEventFlippedOneLoss event g x ≤
      upper * law.acceptedEventFlippedOneLoss event w x := by
  classical
  unfold acceptedEventFlippedOneLoss
  calc
    (∑ mask ∈ event,
      law.weight mask * (∑ j ∈ oneToZeroFlips x mask, g j)) ≤
        ∑ mask ∈ event,
          law.weight mask * (upper * (∑ j ∈ oneToZeroFlips x mask, w j)) := by
      apply Finset.sum_le_sum
      intro mask _
      apply mul_le_mul_of_nonneg_left _ (law.weight_nonneg mask)
      calc
        (∑ j ∈ oneToZeroFlips x mask, g j) ≤
            ∑ j ∈ oneToZeroFlips x mask, upper * w j := by
          apply Finset.sum_le_sum
          intro j _
          exact (hband j).2
        _ = upper * (∑ j ∈ oneToZeroFlips x mask, w j) := by
          rw [Finset.mul_sum]
    _ = upper * (∑ mask ∈ event,
          law.weight mask * (∑ j ∈ oneToZeroFlips x mask, w j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mask _
      ring

/-- Original-law objective-weighted gains dominate original-law losses on
an entirely accepted event, regardless of potential coefficients. -/
theorem acceptedEventFlippedZeroGain_ge_oneLoss_of_accepts {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w : Fin n → ℝ) (x : BitString n)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    law.acceptedEventFlippedOneLoss event w x ≤
      law.acceptedEventFlippedZeroGain event w x := by
  classical
  unfold acceptedEventFlippedOneLoss acceptedEventFlippedZeroGain
  apply Finset.sum_le_sum
  intro mask hm
  exact mul_le_mul_of_nonneg_left
    ((accepts_linearFitness_iff_flip_sums w x mask).1 (hacc mask hm))
    (law.weight_nonneg mask)

/-- Before dropping the objective's nonnegative acceptance margin, the
accepted potential drop retains the exact `lower * objectiveMargin` credit. -/
theorem acceptedEventWeightedPotentialDrop_ge_objectiveMargin_sub_distortionLoss
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (lower upper : ℝ)
    (hband : PotentialWeightSandwich w g lower upper)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    lower * (law.acceptedEventFlippedZeroGain event w x -
        law.acceptedEventFlippedOneLoss event w x) -
      (upper - lower) * law.acceptedEventFlippedOneLoss event w x ≤
        law.acceptedEventWeightedPotentialDrop event w g x := by
  have hgain := law.acceptedEventFlippedZeroGain_ge_scaledObjectiveGain
    event w g x lower upper hband
  have hloss := law.acceptedEventFlippedOneLoss_le_scaledObjectiveLoss
    event w g x lower upper hband
  have hexact := law.acceptedEventWeightedPotentialDrop_eq_zeroGain_sub_oneLoss_of_accepts
    event w g x hacc
  calc
    lower * (law.acceptedEventFlippedZeroGain event w x -
        law.acceptedEventFlippedOneLoss event w x) -
      (upper - lower) * law.acceptedEventFlippedOneLoss event w x =
        lower * law.acceptedEventFlippedZeroGain event w x -
          upper * law.acceptedEventFlippedOneLoss event w x := by ring
    _ ≤ law.acceptedEventFlippedZeroGain event g x -
          law.acceptedEventFlippedOneLoss event g x :=
      sub_le_sub hgain hloss
    _ = law.acceptedEventWeightedPotentialDrop event w g x := hexact.symm

/-- Nonnegative `lower` and objective acceptance allow the entire objective
margin to be discarded, charging only the coefficient distortion. -/
theorem acceptedEventWeightedPotentialDrop_ge_neg_distortionLoss_of_accepts
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) (lower upper : ℝ)
    (hlower : 0 ≤ lower)
    (hband : PotentialWeightSandwich w g lower upper)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    -((upper - lower) * law.acceptedEventFlippedOneLoss event w x) ≤
      law.acceptedEventWeightedPotentialDrop event w g x := by
  have hmargin : 0 ≤ law.acceptedEventFlippedZeroGain event w x -
      law.acceptedEventFlippedOneLoss event w x :=
    sub_nonneg.mpr (law.acceptedEventFlippedZeroGain_ge_oneLoss_of_accepts
      event w x hacc)
  have hscaled : 0 ≤ lower *
      (law.acceptedEventFlippedZeroGain event w x -
        law.acceptedEventFlippedOneLoss event w x) :=
    mul_nonneg hlower hmargin
  have hbound :=
    law.acceptedEventWeightedPotentialDrop_ge_objectiveMargin_sub_distortionLoss
      event w g x lower upper hband hacc
  linarith

/-- Every mask in a short-pivot remainder is accepted. Its signed potential
drop is bounded by distortion times only its *actual* objective loss. -/
theorem shortPivotRemainderEvent_drop_ge_neg_distortionLoss {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (i : Fin n) (lower upper : ℝ) (hlower : 0 ≤ lower)
    (hband : PotentialWeightSandwich w g lower upper) :
    -((upper - lower) *
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) w x) ≤
      law.acceptedEventWeightedPotentialDrop
        (shortPivotRemainderEvent w x b i) w g x := by
  exact law.acceptedEventWeightedPotentialDrop_ge_neg_distortionLoss_of_accepts
    (shortPivotRemainderEvent w x b i) w g x lower upper hlower hband
    (fun mask hm => shortPivotRemainderEvent_accepts w x b i mask hm)

/-- Stage 95's exact singleton-plus-remainder partition, now charging only
objective-weighted losses multiplied by coefficient distortion. -/
theorem acceptedEventWeightedPotentialDrop_short_ge_singleton_sub_distortionLoss
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (lower upper : ℝ) (hlower : 0 ≤ lower)
    (hband : PotentialWeightSandwich w g lower upper) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) -
      (upper - lower) *
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedOneLoss
            (shortPivotRemainderEvent w x b i) w x) ≤
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x := by
  have hsplit := law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_remainders
    hn w g hw x b hb
  have hsum :
      (∑ i ∈ zeroPositions x,
        -((upper - lower) * law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) w x)) ≤
      (∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (shortPivotRemainderEvent w x b i) w g x) := by
    apply Finset.sum_le_sum
    intro i _
    exact law.shortPivotRemainderEvent_drop_ge_neg_distortionLoss
      w g x b i lower upper hlower hband
  have hrewrite :
      (∑ i ∈ zeroPositions x,
        -((upper - lower) * law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) w x)) =
      -((upper - lower) *
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedOneLoss
            (shortPivotRemainderEvent w x b i) w x)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hrewrite] at hsum
  linarith

/-- Recombine the accepted short-radius distortion budget with the Stage 92
high-radius tail-first-moment penalty. No higher moment is presumed finite. -/
theorem linearErrorPotential_drift_ge_singleton_sub_distortionLoss_sub_tail
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (lower upper : ℝ) (hlower : 0 ≤ lower)
    (hband : PotentialWeightSandwich w g lower upper) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) -
      (upper - lower) *
        (∑ i ∈ zeroPositions x,
          law.acceptedEventFlippedOneLoss
            (shortPivotRemainderEvent w x b i) w x) -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) ≤
      driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x := by
  have hg : ∀ j, 0 ≤ g j := by
    intro j
    have hwj : 0 ≤ w j := (hw j).le
    exact (mul_nonneg hlower hwj).trans (hband j).1
  have hshort := law.acceptedEventWeightedPotentialDrop_short_ge_singleton_sub_distortionLoss
    hn w g hw x b hb lower upper hlower hband
  have htail := law.linearErrorPotential_drift_ge_short_sub_tailMeanRadius
    hn w g x b hg
  linarith

/-- Optional coarser numerical corollary: the coefficient sandwich and
positive objective weights imply `lower <= upper` in dimension at least two.
The accepted losses may then be bounded using Stage 94's truncated pair
moment. This may lose sharpness and is not the published runtime bound. -/
theorem linearErrorPotential_drift_ge_singleton_sub_distortionPairBudget_sub_tail
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : ℕ) (hb : 2 ≤ b)
    (lower upper : ℝ) (hlower : 0 ≤ lower)
    (hband : PotentialWeightSandwich w g lower upper) :
    (law.oneBitMass / (n : ℝ)) * (∑ i ∈ zeroPositions x, g i) -
      (upper - lower) *
        (∑ _i ∈ zeroPositions x,
          (law.truncatedSecondFactorialRadiusMoment (b - 1) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
            (∑ j ∈ onePositions x, w j)) -
      (law.tailMeanRadius b / (n : ℝ)) *
        (∑ j ∈ onePositions x, g j) ≤
      driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x := by
  have hpos : 0 < n := by omega
  have hbase := law.linearErrorPotential_drift_ge_singleton_sub_distortionLoss_sub_tail
    hpos w g hw x b hb lower upper hlower hband
  have hcoeff : 0 ≤ upper - lower := by
    let j : Fin n := ⟨0, by omega⟩
    have hprod : lower * w j ≤ upper * w j :=
      (hband j).1.trans (hband j).2
    have hle : lower ≤ upper := by
      by_contra hnot
      have hlt : upper < lower := lt_of_not_ge hnot
      have hprodlt : upper * w j < lower * w j :=
        mul_lt_mul_of_pos_right hlt (hw j)
      exact (not_lt_of_ge hprod) hprodlt
    exact sub_nonneg.mpr hle
  have hbudget :
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) w x) ≤
      (∑ _i ∈ zeroPositions x,
        (law.truncatedSecondFactorialRadiusMoment (b - 1) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
          (∑ j ∈ onePositions x, w j)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact law.shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
      hn w w x b i ((mem_zeroPositions x i).1 hi)
      (fun j => (hw j).le)
  have hmul := mul_le_mul_of_nonneg_left hbudget hcoeff
  linarith

end StaticUnaryUnbiasedMutation
end ECRuntime
