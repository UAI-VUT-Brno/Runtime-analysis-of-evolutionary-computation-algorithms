import ECRuntime.StaticUnaryUnbiasedAcceptedRadiusTail
import ECRuntime.StaticUnaryUnbiasedLinearLossDecomposition
import ECRuntime.StaticUnaryUnbiasedLinearDrift
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 90: signed accepted-tail loss and a first-moment drift envelope

The Stage-89 bound on the *probability* of an accepted long-radius mutation
cannot by itself control its signed potential change. Here we retain the
selected-mask probabilities and explicitly charge any negative contribution
against the one-to-zero flips. For nonnegative potential coefficients this
also gives a conservative bound in terms of the total coefficient mass and
the unconditional first radius moment.

The estimate is intentionally not presented as a positive global drift bound:
the total coefficient mass may grow exponentially with the dimension, and
there is no inequality that replaces this factor using the mean radius alone.
No independent-bit assumption or bounded second factorial moment is used.
-/

/-- For any event consisting of accepted masks, the event-weighted selected
potential change is precisely the signed sum of its left and right terms.
No sign assumption is made on the potential coefficients. -/
theorem acceptedEventWeightedPotentialDrop_eq_leftDelta_add_rightDelta_of_accepts
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (k : Fin n)
    (event : Finset (MutationMask n))
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    law.acceptedEventWeightedPotentialDrop event w g x =
      (∑ mask ∈ event,
        law.weight mask * acceptedLeftDelta g x mask k) +
      (∑ mask ∈ event,
        law.weight mask * acceptedRightDelta g x mask k) := by
  classical
  unfold acceptedEventWeightedPotentialDrop
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro mask hm
  rw [linearErrorPotential_selected_drop_eq_leftDelta_add_rightDelta_of_accepts
    w g x mask k (hacc mask hm)]
  ring

/-- Specialization of the exact signed left/right identity to accepted
high-radius masks. -/
theorem acceptedHighRadiusPotentialDrop_eq_leftDelta_add_rightDelta
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (k : Fin n) (b : ℕ) :
    law.acceptedEventWeightedPotentialDrop
      (acceptedHighRadiusMaskEvent w x b) w g x =
      (∑ mask ∈ acceptedHighRadiusMaskEvent w x b,
        law.weight mask * acceptedLeftDelta g x mask k) +
      (∑ mask ∈ acceptedHighRadiusMaskEvent w x b,
        law.weight mask * acceptedRightDelta g x mask k) := by
  classical
  apply law.acceptedEventWeightedPotentialDrop_eq_leftDelta_add_rightDelta_of_accepts
    w g x k (acceptedHighRadiusMaskEvent w x b)
  intro mask hm
  change mask ∈ (highRadiusMaskEvent (n := n) b).filter
    (fun m => Accepts (linearFitness w) x (mutateWithMask x m)) at hm
  exact (Finset.mem_filter.mp hm).2

/-- An accepted mutation cannot decrease a nonnegative error potential by
more than the potential weight of the coordinates flipped from one to zero.
This pointwise inequality is stronger than a bound by all coefficient mass. -/
theorem linearErrorPotential_selected_drop_ge_neg_oneToZeroLoss_of_accepts
    {n : ℕ} (w g : Fin n → ℝ) (x : BitString n)
    (mask : MutationMask n) (hg : ∀ j, 0 ≤ g j)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    -(∑ j ∈ oneToZeroFlips x mask, g j) ≤
      linearErrorPotential g x -
        linearErrorPotential g
          (selectedAfterMask (linearFitness w) x mask) := by
  rw [linearErrorPotential_selected_drop_of_accepts w g x mask hacc,
    flipContribution_sum_eq_flip_sums]
  have hgain : 0 ≤ ∑ j ∈ zeroToOneFlips x mask, g j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hg j
  linarith

/-- The accepted high-radius signed drift is bounded below by the negative
expected loss over the coordinates actually flipped from one to zero.  This
keeps the acceptance indicator and the full radius distribution intact. -/
theorem acceptedHighRadiusPotentialDrop_ge_neg_flippedOneLoss
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ)
    (hg : ∀ j, 0 ≤ g j) :
    -(∑ mask ∈ acceptedHighRadiusMaskEvent w x b,
      law.weight mask * (∑ j ∈ oneToZeroFlips x mask, g j)) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x := by
  classical
  unfold acceptedEventWeightedPotentialDrop
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro mask hm
  have hacc : Accepts (linearFitness w) x (mutateWithMask x mask) := by
    change mask ∈ (highRadiusMaskEvent (n := n) b).filter
      (fun m => Accepts (linearFitness w) x (mutateWithMask x m)) at hm
    exact (Finset.mem_filter.mp hm).2
  have hdrop := linearErrorPotential_selected_drop_ge_neg_oneToZeroLoss_of_accepts
    w g x mask hg hacc
  have hmul := mul_le_mul_of_nonneg_left hdrop (law.weight_nonneg mask)
  nlinarith

/-- The weighted error potential is at most the sum of all nonnegative
coefficients, regardless of the current search point. -/
theorem linearErrorPotential_le_sum_coefficients {n : ℕ}
    (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j) (x : BitString n) :
    linearErrorPotential g x ≤ ∑ j : Fin n, g j := by
  unfold linearErrorPotential
  apply Finset.sum_le_sum
  intro j hj
  cases hbit : x j with
  | false =>
      simp [bitValueReal]
  | true =>
      simpa [hbit, bitValueReal] using (hg j)

/-- Coarse but unconditional first-moment control of the *signed* accepted
long-radius contribution. The coefficient sum is essential: the Markov
bound on event probability alone is not a signed-drift estimate. -/
theorem acceptedHighRadiusPotentialDrop_ge_neg_firstMomentEnvelope
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n)
    (hg : ∀ j, 0 ≤ g j) {b : ℕ} (hb : 0 < b) :
    -(∑ j : Fin n, g j) * (law.meanRadius / (b : ℝ)) ≤
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x := by
  classical
  let event := acceptedHighRadiusMaskEvent w x b
  let G : ℝ := ∑ j : Fin n, g j
  have hG : 0 ≤ G := by
    dsimp [G]
    apply Finset.sum_nonneg
    intro j hj
    exact hg j
  have hmass := law.acceptedHighRadiusMaskEvent_mass_le_meanRadius_div
    w x hb
  have hmassLower : -G * (law.meanRadius / (b : ℝ)) ≤
      -G * law.maskEventMass event :=
    mul_le_mul_of_nonpos_left hmass (by linarith : -G ≤ 0)
  have hpoint (mask : MutationMask n) :
      -G ≤ linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) := by
    have hparent := linearErrorPotential_nonneg g hg x
    have hchild := linearErrorPotential_le_sum_coefficients g hg
      (selectedAfterMask (linearFitness w) x mask)
    dsimp [G]
    linarith
  have hweighted :
      -G * law.maskEventMass event ≤
        law.acceptedEventWeightedPotentialDrop event w g x := by
    unfold maskEventMass acceptedEventWeightedPotentialDrop
    calc
      -G * (∑ mask ∈ event, law.weight mask) =
          ∑ mask ∈ event, law.weight mask * (-G) := by
            calc
              -G * (∑ mask ∈ event, law.weight mask) =
                  (∑ mask ∈ event, law.weight mask) * (-G) := by ring
              _ = ∑ mask ∈ event, law.weight mask * (-G) := by
                    rw [Finset.sum_mul]
      _ ≤ ∑ mask ∈ event,
            law.weight mask *
              (linearErrorPotential g x -
                linearErrorPotential g
                  (selectedAfterMask (linearFitness w) x mask)) := by
            apply Finset.sum_le_sum
            intro mask hm
            exact mul_le_mul_of_nonneg_left
              (hpoint mask) (law.weight_nonneg mask)
  exact hmassLower.trans hweighted

/-- The exact Stage-89 short/long decomposition and the first-moment signed
tail estimate give a global (possibly negative) drift lower envelope.
No positive multiplicative drift is claimed from the mean alone. -/
theorem acceptedEventWeightedPotentialDrop_univ_ge_short_sub_firstMomentEnvelope
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n)
    (hg : ∀ j, 0 ≤ g j) {b : ℕ} (hb : 0 < b) :
    law.acceptedEventWeightedPotentialDrop Finset.univ w g x ≥
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x -
      (∑ j : Fin n, g j) * (law.meanRadius / (b : ℝ)) := by
  rw [law.acceptedEventWeightedPotentialDrop_univ_eq_shortRadius_add_highRadius
    w g x b,
    law.acceptedEventWeightedPotentialDrop_highRadius_eq_acceptedHighRadius
      w g x b]
  have htail := law.acceptedHighRadiusPotentialDrop_ge_neg_firstMomentEnvelope
    w g x hg hb
  linarith

/-- The same first-moment bound stated for the actual Markov-kernel drift.
The short-radius term is retained as a signed expectation. -/
theorem linearErrorPotential_drift_ge_short_sub_firstMomentEnvelope
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n)
    (hg : ∀ j, 0 ≤ g j) {b : ℕ} (hb : 0 < b) :
    driftAt (law.transition (linearFitness w))
        (linearErrorPotential g) x ≥
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x -
      (∑ j : Fin n, g j) * (law.meanRadius / (b : ℝ)) := by
  rw [law.drift_eq_mask_sum]
  exact law.acceptedEventWeightedPotentialDrop_univ_ge_short_sub_firstMomentEnvelope
    w g x hg hb

end StaticUnaryUnbiasedMutation
end ECRuntime
