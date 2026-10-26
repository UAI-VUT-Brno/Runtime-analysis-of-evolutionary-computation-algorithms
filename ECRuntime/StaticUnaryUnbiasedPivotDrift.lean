import ECRuntime.StaticUnaryUnbiasedEventWeightedRightLoss
import ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Corrected event-restricted potential drift at an accepted pivot

Stage 79 supplies the event-weighted left contribution of the corrected potential,
and Stage 80 supplies the signed event-weighted right contribution. Both estimates
use the factorial-moment-calibrated potential, not an unproved mean-radius-only
conditional probability estimate. The present stage combines them through the
exact Stage-75 pointwise left/right decomposition.

The event-weighted drop here is an *unnormalized* expectation: every mutation mask
in the accepted pivot event is charged by its original law weight. There is no
division by the event probability, and there is no assumption that masks arise
from independent flips. The resulting lower bound applies only to the particular
accepted pivot event, not to the drift across all mutation masks.

The three declarations below preserve the Stage-81 statement proposal:
(1) exact weighted L + R; (2) the corrected per-pivot bound; and
(3) its nonnegativity for slack at least one. Global drift requires a further
proof that the pivot events partition all nontrivial accepted mutations.
-/

/-- The unnormalized expected potential decrease restricted to a finite mask event. -/
noncomputable def acceptedEventWeightedPotentialDrop {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ event, law.weight mask *
    (linearErrorPotential g x -
      linearErrorPotential g (selectedAfterMask (linearFitness w) x mask))

/-- Exact event-weighted L/R decomposition on the accepted pivot event. -/
theorem acceptedLeftmostZeroEvent_weightedPotentialDrop_eq_left_add_right
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (i k : Fin n) :
    law.acceptedEventWeightedPotentialDrop (acceptedLeftmostZeroEvent w x i) w g x =
      law.acceptedLeftWeightedContribution
        (acceptedLeftmostZeroEvent w x i) g x k +
      law.acceptedRightWeightedContribution
        (acceptedLeftmostZeroEvent w x i) g x k := by
  classical
  unfold acceptedEventWeightedPotentialDrop acceptedLeftWeightedContribution
    acceptedRightWeightedContribution
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  rw [acceptedLeftmostZeroEvent_selected_drop_eq_leftDelta_add_rightDelta
    w g x i k mask hmask]
  ring

/-- The corrected factorial-moment route gives the per-pivot expected decrease. -/
theorem acceptedLeftmostZeroEvent_correctedWeightedPotentialDrop_lower_bound
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    (law.oneBitMass / (n : ℝ)) *
        ((1 - 1 / alpha) * law.correctedPotentialWeight alpha w i) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedLeftmostZeroEvent w x i) w
        (law.correctedPotentialWeight alpha w) x := by
  have hleft :=
    law.singletonRate_mul_correctedWeight_le_acceptedLeftWeightedContribution
      (le_of_lt halpha) w hw hmono x i hi
  have hright :=
    law.neg_singletonRate_correctedWeight_div_le_acceptedRightWeightedContribution
      hn hp1 halpha w hw hmono x i hi
  have hdecomp :=
    law.acceptedLeftmostZeroEvent_weightedPotentialDrop_eq_left_add_right
      w (law.correctedPotentialWeight alpha w) x i
      (law.correctedAnchor alpha w i)
  calc
    (law.oneBitMass / (n : ℝ)) *
        ((1 - 1 / alpha) * law.correctedPotentialWeight alpha w i) =
      (law.oneBitMass / (n : ℝ)) * law.correctedPotentialWeight alpha w i +
        -((law.oneBitMass / (n : ℝ)) *
          (law.correctedPotentialWeight alpha w i / alpha)) := by ring
    _ ≤ law.acceptedLeftWeightedContribution
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) +
      law.acceptedRightWeightedContribution
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) := add_le_add hleft hright
    _ = law.acceptedEventWeightedPotentialDrop
        (acceptedLeftmostZeroEvent w x i) w
        (law.correctedPotentialWeight alpha w) x := hdecomp.symm

/-- For slack at least one, the accepted pivot event has nonnegative mean drop. -/
theorem acceptedLeftmostZeroEvent_correctedWeightedPotentialDrop_nonneg
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 1 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    0 ≤ law.acceptedEventWeightedPotentialDrop
      (acceptedLeftmostZeroEvent w x i) w
      (law.correctedPotentialWeight alpha w) x := by
  have halphaPos : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  have hfactor : 0 ≤ (1 : ℝ) - 1 / alpha := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ halphaPos).2
    simpa using halpha
  have hrate : 0 ≤ law.oneBitMass / (n : ℝ) :=
    div_nonneg (le_of_lt hp1) (Nat.cast_nonneg n)
  have hweight : 0 ≤ law.correctedPotentialWeight alpha w i :=
    law.correctedPotentialWeight_nonneg (le_of_lt halphaPos) w hw hmono i
  calc
    0 ≤ (law.oneBitMass / (n : ℝ)) *
        ((1 - 1 / alpha) * law.correctedPotentialWeight alpha w i) :=
      mul_nonneg hrate (mul_nonneg hfactor hweight)
    _ ≤ law.acceptedEventWeightedPotentialDrop
        (acceptedLeftmostZeroEvent w x i) w
        (law.correctedPotentialWeight alpha w) x :=
      law.acceptedLeftmostZeroEvent_correctedWeightedPotentialDrop_lower_bound
        hn hp1 halphaPos w hw hmono x i hi

end StaticUnaryUnbiasedMutation
end ECRuntime
