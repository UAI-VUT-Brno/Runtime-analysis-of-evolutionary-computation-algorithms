import ECRuntime.StaticUnaryUnbiasedCorrectedGammaTail
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Corrected left-gain geometry and event-weighted singleton contribution

Stage 78 fix 2 compiler-promoted the corrected geometric-tail layer and left the
accepted-event drift assembly as the next boundary.  Before the right-loss estimate can
be subtracted from the singleton pivot gain, one needs the literature's implicit fact
that the `L` contribution is nonnegative on every accepted pivot mask.

For the corrected suffix-min potential this follows from two ratio-envelope facts.
Writing `g` for `correctedPotentialWeight` and `a(i)` for `correctedAnchor`:

* on the pivot suffix, `g_i / w_i <= g_q / w_q` whenever `i <= q`;
* to the left of the anchor, `g_j / w_j <= g_i / w_i` whenever `j <= a(i)`.

The first fact controls every zero-to-one gain in an accepted pivot event, because the
pivot is the most-important flipped zero.  The second controls every one-to-zero loss in
the Stage-75 left region.  Objective acceptance then implies `acceptedLeftDelta >= 0`.

The module also isolates the singleton mask inside the finite pivot event and proves the
event-weighted left contribution is at least

`(p₁ / n) * g_i`.

This is the corrected formal counterpart of the positive term extracted in equation (22)
of the literature proof.  The next stage can combine it algebraically with the promoted
Stage-78 right-loss bound.
-/

/-- Along a suffix, the corrected potential-to-objective ratio is nondecreasing. -/
theorem correctedPotentialWeight_div_weight_mono_suffix {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (i q : Fin n) (hiq : i.val ≤ q.val) :
    law.correctedPotentialWeight alpha w i / w i ≤
      law.correctedPotentialWeight alpha w q / w q := by
  let a : Fin n := law.correctedAnchor alpha w q
  have hqa : q.val ≤ a.val := by
    dsimp [a]
    exact law.correctedAnchor_ge alpha w q
  have hia : i.val ≤ a.val := hiq.trans hqa
  have hmin := law.correctedPotentialWeight_le_clipCandidate alpha w i a hia
  have hwi : 0 < w i := hw i
  have hwq : 0 < w q := hw q
  have hwa : 0 < w a := hw a
  have hleft :
      law.correctedPotentialWeight alpha w i / w i ≤
        law.correctedGammaWeight alpha a / w a := by
    apply (div_le_iff₀ hwi).2
    calc
      law.correctedPotentialWeight alpha w i ≤
          law.correctedGammaWeight alpha a * (w i / w a) := by
        simpa [correctedClipCandidate] using hmin
      _ = (law.correctedGammaWeight alpha a / w a) * w i := by
        ring
  have hright :
      law.correctedPotentialWeight alpha w q / w q =
        law.correctedGammaWeight alpha a / w a := by
    rw [law.correctedPotentialWeight_eq_anchor_formula alpha w q]
    change
      (law.correctedGammaWeight alpha a * (w q / w a)) / w q =
        law.correctedGammaWeight alpha a / w a
    field_simp [ne_of_gt hwq, ne_of_gt hwa]
  calc
    law.correctedPotentialWeight alpha w i / w i ≤
        law.correctedGammaWeight alpha a / w a := hleft
    _ = law.correctedPotentialWeight alpha w q / w q := hright.symm

/-- Every coordinate in the left region of the pivot anchor has ratio at most the pivot ratio. -/
theorem correctedPotentialWeight_div_weight_le_pivotRatio_of_le_anchor {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (i j : Fin n)
    (hja : j.val ≤ (law.correctedAnchor alpha w i).val) :
    law.correctedPotentialWeight alpha w j / w j ≤
      law.correctedPotentialWeight alpha w i / w i := by
  let a : Fin n := law.correctedAnchor alpha w i
  have hmin := law.correctedPotentialWeight_le_clipCandidate alpha w j a (by
    simpa [a] using hja)
  have hwj : 0 < w j := hw j
  have hwi : 0 < w i := hw i
  have hwa : 0 < w a := hw a
  have hleft :
      law.correctedPotentialWeight alpha w j / w j ≤
        law.correctedGammaWeight alpha a / w a := by
    apply (div_le_iff₀ hwj).2
    calc
      law.correctedPotentialWeight alpha w j ≤
          law.correctedGammaWeight alpha a * (w j / w a) := by
        simpa [correctedClipCandidate] using hmin
      _ = (law.correctedGammaWeight alpha a / w a) * w j := by
        ring
  have hpivot :
      law.correctedPotentialWeight alpha w i / w i =
        law.correctedGammaWeight alpha a / w a := by
    rw [law.correctedPotentialWeight_eq_anchor_formula alpha w i]
    change
      (law.correctedGammaWeight alpha a * (w i / w a)) / w i =
        law.correctedGammaWeight alpha a / w a
    field_simp [ne_of_gt hwi, ne_of_gt hwa]
  calc
    law.correctedPotentialWeight alpha w j / w j ≤
        law.correctedGammaWeight alpha a / w a := hleft
    _ = law.correctedPotentialWeight alpha w i / w i := hpivot.symm

/-- On a pivot event, corrected gain dominates the pivot ratio times objective gain. -/
theorem pivotRatio_mul_objectiveGain_le_correctedGain {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    (law.correctedPotentialWeight alpha w i / w i) *
        (∑ q ∈ zeroToOneFlips x mask, w q) ≤
      acceptedGain (law.correctedPotentialWeight alpha w) x mask := by
  unfold acceptedGain
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hiq : i.val ≤ q.val :=
    acceptedLeftmostZeroEvent_pivot_le w x i mask hmask q hq
  have hratio := law.correctedPotentialWeight_div_weight_mono_suffix
    alpha w hw i q hiq
  exact (le_div_iff₀ (hw q)).1 hratio

/-- The corrected left loss is bounded by the pivot ratio times total objective loss. -/
theorem correctedLeftLoss_le_pivotRatio_mul_objectiveLoss {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    acceptedLeftLoss (law.correctedPotentialWeight alpha w) x mask
        (law.correctedAnchor alpha w i) ≤
      (law.correctedPotentialWeight alpha w i / w i) *
        (∑ j ∈ oneToZeroFlips x mask, w j) := by
  classical
  let c : ℝ := law.correctedPotentialWeight alpha w i / w i
  have hgi : 0 ≤ law.correctedPotentialWeight alpha w i :=
    zero_le_one.trans
      (law.one_le_correctedPotentialWeight halpha w hw hmono i)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg hgi (hw i).le
  unfold acceptedLeftLoss oneToZeroFlips
  change
    (∑ j : Fin n,
      if j ∈ mask ∧ x j = true ∧
          j.val ≤ (law.correctedAnchor alpha w i).val
        then law.correctedPotentialWeight alpha w j else 0) ≤
      c * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ∈ mask ∧ x j = true), w j
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hm : j ∈ mask
  · cases hx : x j with
    | false =>
        simp [hm]
    | true =>
        by_cases hja : j.val ≤ (law.correctedAnchor alpha w i).val
        · have hratio :=
            law.correctedPotentialWeight_div_weight_le_pivotRatio_of_le_anchor
              alpha w hw i j hja
          have hscaled : law.correctedPotentialWeight alpha w j ≤ c * w j := by
            dsimp [c]
            exact (div_le_iff₀ (hw j)).1 hratio
          simpa [hm, hx, hja] using hscaled
        · have hprod : 0 ≤ c * w j := mul_nonneg hc (hw j).le
          simpa [hm, hx, hja] using hprod
  · simp [hm]

/-- The literature's `L` contribution is pointwise nonnegative on every accepted pivot mask. -/
theorem acceptedLeftmostZeroEvent_correctedLeftDelta_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    0 ≤ acceptedLeftDelta (law.correctedPotentialWeight alpha w) x mask
      (law.correctedAnchor alpha w i) := by
  let c : ℝ := law.correctedPotentialWeight alpha w i / w i
  have hgi : 0 ≤ law.correctedPotentialWeight alpha w i :=
    zero_le_one.trans
      (law.one_le_correctedPotentialWeight halpha w hw hmono i)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg hgi (hw i).le
  have hbalance :=
    (accepts_linearFitness_iff_flip_sums w x mask).1
      (acceptedLeftmostZeroEvent_accepts w x i mask hmask)
  have hscaledBalance :
      c * (∑ j ∈ oneToZeroFlips x mask, w j) ≤
        c * (∑ q ∈ zeroToOneFlips x mask, w q) :=
    mul_le_mul_of_nonneg_left hbalance hc
  have hloss := law.correctedLeftLoss_le_pivotRatio_mul_objectiveLoss
    halpha w hw hmono x i mask
  have hgain := law.pivotRatio_mul_objectiveGain_le_correctedGain
    alpha w hw x i mask hmask
  have hleftLeGain :
      acceptedLeftLoss (law.correctedPotentialWeight alpha w) x mask
          (law.correctedAnchor alpha w i) ≤
        acceptedGain (law.correctedPotentialWeight alpha w) x mask := by
    exact hloss.trans (hscaledBalance.trans hgain)
  unfold acceptedLeftDelta
  exact sub_nonneg.mpr hleftLeGain

/-- A singleton zero-to-one pivot contributes exactly its corrected potential coefficient to `L`. -/
theorem acceptedLeftDelta_singleton_zero_eq {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (i k : Fin n) (hi : x i = false) :
    acceptedLeftDelta g x ({i} : MutationMask n) k = g i := by
  classical
  have hzero : zeroToOneFlips x ({i} : MutationMask n) = {i} := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [zeroToOneFlips, hi]
    · simp [zeroToOneFlips, hji]
  have hloss : acceptedLeftLoss g x ({i} : MutationMask n) k = 0 := by
    unfold acceptedLeftLoss
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [hji]
  unfold acceptedLeftDelta acceptedGain
  rw [hzero, hloss]
  simp

/-- Event-weighted `L` contribution over a finite mask event. -/
noncomputable def acceptedLeftWeightedContribution {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) : ℝ :=
  ∑ mask ∈ event, law.weight mask * acceptedLeftDelta g x mask k

/--
The accepted pivot event carries at least the singleton-rate corrected gain
`(p₁/n) * g_i` in its event-weighted left contribution.
-/
theorem singletonRate_mul_correctedWeight_le_acceptedLeftWeightedContribution {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    (law.oneBitMass / (n : ℝ)) * law.correctedPotentialWeight alpha w i ≤
      law.acceptedLeftWeightedContribution
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) := by
  have hn : 0 < n := by
    have hiLt : i.val < n := i.isLt
    omega
  have hsingleton :
      ({i} : MutationMask n) ∈ acceptedLeftmostZeroEvent w x i :=
    singleton_mem_acceptedLeftmostZeroEvent w hw x i hi
  have hsingleLe :
      law.weight ({i} : MutationMask n) *
          acceptedLeftDelta (law.correctedPotentialWeight alpha w) x
            ({i} : MutationMask n) (law.correctedAnchor alpha w i) ≤
        law.acceptedLeftWeightedContribution
          (acceptedLeftmostZeroEvent w x i)
          (law.correctedPotentialWeight alpha w) x
          (law.correctedAnchor alpha w i) := by
    unfold acceptedLeftWeightedContribution
    exact Finset.single_le_sum
      (fun mask hmask =>
        mul_nonneg (law.weight_nonneg mask)
          (law.acceptedLeftmostZeroEvent_correctedLeftDelta_nonneg
            halpha w hw hmono x i mask hmask))
      hsingleton
  rw [law.singletonWeight_eq_oneBitMass_div hn i] at hsingleLe
  rw [acceptedLeftDelta_singleton_zero_eq
    (law.correctedPotentialWeight alpha w) x i
    (law.correctedAnchor alpha w i) hi] at hsingleLe
  exact hsingleLe

end StaticUnaryUnbiasedMutation
end ECRuntime
