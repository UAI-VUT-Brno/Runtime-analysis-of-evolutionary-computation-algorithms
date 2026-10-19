import ECRuntime.StaticUnaryUnbiasedCorrectedPotential
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Corrected-potential anchor envelope and accepted-event instantiation

Stage 76 compiler-promoted the corrected penalty ratio, geometric baseline, suffix-min
objective clipping, and a concrete minimizing suffix coordinate `correctedAnchor`.
Stage 75 already provides the accepted-event `L/R` decomposition and the corrected
factorial-moment right-loss proxy for an arbitrary anchor and arbitrary nonnegative
potential coefficients.

This module connects those two promoted interfaces without yet evaluating the geometric
tail in closed form.  It proves:

* the clipped coefficient is exactly the contact candidate at its chosen anchor;
* under positive nonincreasing objective weights, the anchor gamma coefficient is no
  larger than the clipped coefficient at the pivot;
* the exact accepted `L/R` decomposition specialized to the corrected potential/anchor;
* the Stage-75 conditional right-loss bound specialized to the corrected coefficients;
* the whole right-region corrected-weight mass is bounded by the geometric gamma tail.

The next stage may therefore focus only on the finite geometric-tail calculation and the
resulting per-pivot drift inequality.  No mean-only replacement of the verified
factorial-moment coefficient is used here.
-/

/-- The suffix-min clipped coefficient is exactly its chosen anchor contact candidate. -/
theorem correctedPotentialWeight_eq_anchor_formula {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i : Fin n) :
    law.correctedPotentialWeight alpha w i =
      law.correctedGammaWeight alpha (law.correctedAnchor alpha w i) *
        (w i / w (law.correctedAnchor alpha w i)) := by
  rfl

/-- Corrected clipped coefficients are nonnegative under the calibrated objective assumptions. -/
theorem correctedPotentialWeight_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    0 ≤ law.correctedPotentialWeight alpha w i := by
  exact zero_le_one.trans
    (law.one_le_correctedPotentialWeight halpha w hw hmono i)

/--
The gamma value at the chosen suffix anchor is below the clipped coefficient at the pivot.
This is the inequality needed before converting the right-region loss into a geometric tail.
-/
theorem correctedGammaWeight_anchor_le_correctedPotentialWeight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    law.correctedGammaWeight alpha (law.correctedAnchor alpha w i) ≤
      law.correctedPotentialWeight alpha w i := by
  rw [law.correctedPotentialWeight_eq_anchor_formula alpha w i]
  have hia : i.val ≤ (law.correctedAnchor alpha w i).val :=
    law.correctedAnchor_ge alpha w i
  have hwa : 0 < w (law.correctedAnchor alpha w i) :=
    hw (law.correctedAnchor alpha w i)
  have hwle : w (law.correctedAnchor alpha w i) ≤ w i :=
    hmono i (law.correctedAnchor alpha w i) hia
  have hratio : 1 ≤ w i / w (law.correctedAnchor alpha w i) := by
    apply (le_div_iff₀ hwa).2
    simpa using hwle
  have hgamma0 : 0 ≤
      law.correctedGammaWeight alpha (law.correctedAnchor alpha w i) :=
    zero_le_one.trans
      (law.one_le_correctedGammaWeight halpha (law.correctedAnchor alpha w i))
  have hmul := mul_le_mul_of_nonneg_left hratio hgamma0
  simpa using hmul

/-- Pure geometric suffix tail strictly to the right of an anchor coordinate. -/
noncomputable def correctedGammaTail {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) (k : Fin n) : ℝ :=
  ∑ j ∈ (Finset.univ.filter (fun j : Fin n => k.val < j.val)),
    law.correctedGammaWeight alpha j

/-- The corrected gamma tail is nonnegative for nonnegative slack. -/
theorem correctedGammaTail_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (k : Fin n) :
    0 ≤ law.correctedGammaTail alpha k := by
  unfold correctedGammaTail
  apply Finset.sum_nonneg
  intro j hj
  exact zero_le_one.trans (law.one_le_correctedGammaWeight halpha j)

/-- Corrected weights on the accepted right region are pointwise bounded by gamma weights. -/
theorem acceptedRightRegion_correctedWeight_sum_le_gamma_sum {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (k : Fin n) :
    (∑ j ∈ acceptedRightRegion x k,
      law.correctedPotentialWeight alpha w j) ≤
      ∑ j ∈ acceptedRightRegion x k,
        law.correctedGammaWeight alpha j := by
  apply Finset.sum_le_sum
  intro j hj
  exact law.correctedPotentialWeight_le_gamma alpha w hw j

/-- Dropping the state-bit restriction enlarges the nonnegative gamma right-region sum. -/
theorem acceptedRightRegion_gamma_sum_le_correctedGammaTail {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (x : BitString n) (k : Fin n) :
    (∑ j ∈ acceptedRightRegion x k,
      law.correctedGammaWeight alpha j) ≤
      law.correctedGammaTail alpha k := by
  unfold correctedGammaTail
  have hsub : acceptedRightRegion x k ⊆
      Finset.univ.filter (fun j : Fin n => k.val < j.val) := by
    intro j hj
    have hjdata := (mem_acceptedRightRegion_iff x k j).1 hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjdata.2⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro j hjBig hjSmall
  exact zero_le_one.trans (law.one_le_correctedGammaWeight halpha j)

/-- The whole corrected right-region weight is bounded by the pure geometric suffix tail. -/
theorem acceptedRightRegion_correctedWeight_sum_le_correctedGammaTail {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (k : Fin n) :
    (∑ j ∈ acceptedRightRegion x k,
      law.correctedPotentialWeight alpha w j) ≤
      law.correctedGammaTail alpha k := by
  exact (law.acceptedRightRegion_correctedWeight_sum_le_gamma_sum alpha w hw x k).trans
    (law.acceptedRightRegion_gamma_sum_le_correctedGammaTail halpha x k)

/-- Exact accepted `L/R` decomposition at the corrected anchor and corrected potential. -/
theorem acceptedLeftmostZeroEvent_corrected_drop_eq_leftDelta_add_rightDelta {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    law.correctedLinearPotential alpha w x -
        law.correctedLinearPotential alpha w
          (selectedAfterMask (linearFitness w) x mask) =
      acceptedLeftDelta (law.correctedPotentialWeight alpha w) x mask
          (law.correctedAnchor alpha w i) +
        acceptedRightDelta (law.correctedPotentialWeight alpha w) x mask
          (law.correctedAnchor alpha w i) := by
  simpa [correctedLinearPotential] using
    (acceptedLeftmostZeroEvent_selected_drop_eq_leftDelta_add_rightDelta
      w (law.correctedPotentialWeight alpha w) x i
      (law.correctedAnchor alpha w i) mask hmask)

/-- Stage-75 right-loss proxy specialized to the corrected coefficients and corrected anchor. -/
theorem acceptedLeftmostZeroEvent_correctedRightConditionalLossProxy_le {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    law.acceptedRightConditionalLossProxy
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) ≤
      ∑ j ∈ acceptedRightRegion x (law.correctedAnchor alpha w i),
        law.correctedPotentialWeight alpha w j *
          (law.secondFactorialRadiusMoment /
            (law.oneBitMass * ((n - 1 : ℕ) : ℝ))) := by
  exact law.acceptedLeftmostZeroEvent_rightConditionalLossProxy_le
    hn hp1 w hw x i hi (law.correctedPotentialWeight alpha w)
    (law.correctedPotentialWeight_nonneg halpha w hw hmono)
    (law.correctedAnchor alpha w i)

/--
Drift-ready right-loss envelope: the conditional right-loss proxy is at most the pure
gamma tail times the verified factorial-moment coefficient.
-/
theorem acceptedLeftmostZeroEvent_correctedRightConditionalLossProxy_le_gammaTail {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    law.acceptedRightConditionalLossProxy
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) ≤
      law.correctedGammaTail alpha (law.correctedAnchor alpha w i) *
        (law.secondFactorialRadiusMoment /
          (law.oneBitMass * ((n - 1 : ℕ) : ℝ))) := by
  let coeff : ℝ := law.secondFactorialRadiusMoment /
    (law.oneBitMass * ((n - 1 : ℕ) : ℝ))
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    exact div_nonneg law.secondFactorialRadiusMoment_nonneg
      (mul_nonneg (le_of_lt hp1) (Nat.cast_nonneg _))
  have hproxy := law.acceptedLeftmostZeroEvent_correctedRightConditionalLossProxy_le
    hn hp1 halpha w hw hmono x i hi
  have hweights := law.acceptedRightRegion_correctedWeight_sum_le_correctedGammaTail
    halpha w hw x (law.correctedAnchor alpha w i)
  calc
    law.acceptedRightConditionalLossProxy
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) ≤
      ∑ j ∈ acceptedRightRegion x (law.correctedAnchor alpha w i),
        law.correctedPotentialWeight alpha w j * coeff := by
          simpa [coeff] using hproxy
    _ = (∑ j ∈ acceptedRightRegion x (law.correctedAnchor alpha w i),
          law.correctedPotentialWeight alpha w j) * coeff := by
          rw [Finset.sum_mul]
    _ ≤ law.correctedGammaTail alpha (law.correctedAnchor alpha w i) * coeff :=
      mul_le_mul_of_nonneg_right hweights hcoeff
    _ = law.correctedGammaTail alpha (law.correctedAnchor alpha w i) *
        (law.secondFactorialRadiusMoment /
          (law.oneBitMass * ((n - 1 : ℕ) : ℝ))) := by
          rfl

end StaticUnaryUnbiasedMutation
end ECRuntime
