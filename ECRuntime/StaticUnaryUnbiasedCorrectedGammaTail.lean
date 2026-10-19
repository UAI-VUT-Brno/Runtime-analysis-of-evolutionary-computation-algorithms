import ECRuntime.StaticUnaryUnbiasedCorrectedPotentialEnvelope
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Closed corrected gamma tail and drift-ready right-loss scaling

Stage 77 fix 1 compiler-promoted the corrected anchor envelope and reduced the
conditional right-region loss to the pure gamma suffix tail

`correctedGammaTail alpha k`.

This module closes that remaining finite geometric calculation.  Writing

`rho = correctedPenaltyRatio`

and `base = 1 + alpha * rho`, it proves the exact identity

`GammaTail(k) * (alpha * rho) = gamma_k - 1`.

For positive `alpha` this gives

`rho * GammaTail(k) <= gamma_k / alpha`,

and at the corrected anchor the Stage-77 inequality `gamma_anchor <= g_i` yields

`rho * GammaTail(anchor(i)) <= g_i / alpha`.

Finally, the promoted calibration identity converts the Stage-77 conditional
right-loss envelope into singleton-rate units.  This is the drift-ready negative
term needed before the objective-specific left-gain/event-mass assembly.
-/

/-- Reverse the strict suffix after `k` into exponents `0, ..., n-2-k`. -/
private noncomputable def correctedTailIndexEquiv {n : ℕ} (k : Fin n) :
    {j : Fin n // k.val < j.val} ≃ Fin (n - 1 - k.val) where
  toFun j :=
    ⟨n - 1 - j.1.val, by
      have hjlt : j.1.val < n := j.1.isLt
      have hkj : k.val < j.1.val := j.2
      omega⟩
  invFun r := by
    have hklt : k.val < n := k.isLt
    have hrlt : r.val < n - 1 - k.val := r.isLt
    have hjlt : n - 1 - r.val < n := by
      omega
    have hkj : k.val < n - 1 - r.val := by
      omega
    exact ⟨⟨n - 1 - r.val, hjlt⟩, hkj⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    change n - 1 - (n - 1 - j.1.val) = j.1.val
    have hjlt : j.1.val < n := j.1.isLt
    omega
  right_inv r := by
    apply Fin.ext
    change n - 1 - (n - 1 - r.val) = r.val
    have hklt : k.val < n := k.isLt
    have hrlt : r.val < n - 1 - k.val := r.isLt
    omega

/-- The promoted filtered gamma tail is the ordinary finite geometric sum with
`n-1-k` terms. -/
theorem correctedGammaTail_eq_fin_sum {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) (k : Fin n) :
    law.correctedGammaTail alpha k =
      ∑ r : Fin (n - 1 - k.val), law.correctedGammaBase alpha ^ r.val := by
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun j : Fin n => k.val < j.val)
  have hs : ∀ j : Fin n, j ∈ s ↔ k.val < j.val := by
    intro j
    simp [s]
  have hsub :
      s.sum (fun j : Fin n => law.correctedGammaWeight alpha j) =
        ∑ q : {j : Fin n // k.val < j.val},
          law.correctedGammaWeight alpha q.1 := by
    exact Finset.sum_subtype s hs
      (fun j : Fin n => law.correctedGammaWeight alpha j)
  unfold correctedGammaTail
  change s.sum (fun j : Fin n => law.correctedGammaWeight alpha j) = _
  rw [hsub]
  refine Fintype.sum_equiv (correctedTailIndexEquiv k)
    (fun q : {j : Fin n // k.val < j.val} =>
      law.correctedGammaWeight alpha q.1)
    (fun r : Fin (n - 1 - k.val) => law.correctedGammaBase alpha ^ r.val) ?_
  intro q
  rfl

/-- Multiplication form of a finite geometric power sum. -/
private theorem fin_sum_pow_mul_sub_one (r : ℝ) (m : ℕ) :
    (∑ i : Fin m, r ^ i.val) * (r - 1) = r ^ m - 1 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have hshift :
          (∑ i : Fin m, r ^ (i.succ).val) =
            r * ∑ i : Fin m, r ^ i.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [show (i.succ).val = i.val + 1 by rfl]
        rw [pow_succ]
        ring
      rw [hshift]
      simp only [Fin.val_zero, pow_zero]
      calc
        (1 + r * ∑ i : Fin m, r ^ i.val) * (r - 1) =
            (r - 1) + r * ((∑ i : Fin m, r ^ i.val) * (r - 1)) := by
          ring
        _ = (r - 1) + r * (r ^ m - 1) := by rw [ih]
        _ = r ^ (m + 1) - 1 := by rw [pow_succ]; ring

/-- Exact multiplication-form closed identity for the corrected gamma suffix tail. -/
theorem correctedGammaTail_mul_base_sub_one {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) (k : Fin n) :
    law.correctedGammaTail alpha k * (law.correctedGammaBase alpha - 1) =
      law.correctedGammaWeight alpha k - 1 := by
  rw [law.correctedGammaTail_eq_fin_sum alpha k]
  simpa [correctedGammaWeight] using
    fin_sum_pow_mul_sub_one
      (law.correctedGammaBase alpha) (n - 1 - k.val)

/-- Since `base - 1 = alpha * rho`, the gamma tail has the exact calibrated scaling. -/
theorem correctedGammaTail_mul_alpha_penaltyRatio {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) (k : Fin n) :
    law.correctedGammaTail alpha k *
        (alpha * law.correctedPenaltyRatio) =
      law.correctedGammaWeight alpha k - 1 := by
  have h := law.correctedGammaTail_mul_base_sub_one alpha k
  have hbase :
      law.correctedGammaBase alpha - 1 =
        alpha * law.correctedPenaltyRatio := by
    unfold correctedGammaBase
    ring
  rw [hbase] at h
  exact h

/-- Division form of the calibrated tail identity for nonzero slack. -/
theorem correctedGammaTail_mul_penaltyRatio_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) (halpha : alpha ≠ 0)
    (k : Fin n) :
    law.correctedGammaTail alpha k * law.correctedPenaltyRatio =
      (law.correctedGammaWeight alpha k - 1) / alpha := by
  apply (eq_div_iff halpha).2
  calc
    (law.correctedGammaTail alpha k * law.correctedPenaltyRatio) * alpha =
        law.correctedGammaTail alpha k *
          (alpha * law.correctedPenaltyRatio) := by ring
    _ = law.correctedGammaWeight alpha k - 1 :=
      law.correctedGammaTail_mul_alpha_penaltyRatio alpha k

/-- Positive slack bounds the penalty-scaled suffix tail by `gamma_k / alpha`. -/
theorem correctedGammaTail_mul_penaltyRatio_le_gamma_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 < alpha)
    (k : Fin n) :
    law.correctedGammaTail alpha k * law.correctedPenaltyRatio ≤
      law.correctedGammaWeight alpha k / alpha := by
  rw [law.correctedGammaTail_mul_penaltyRatio_eq alpha (ne_of_gt halpha) k]
  apply (div_le_div_iff_of_pos_right halpha).2
  linarith

/-- At the corrected anchor, the penalty-scaled gamma tail is controlled by `g_i/alpha`. -/
theorem correctedPenaltyRatio_mul_gammaTail_anchor_le_weight_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    law.correctedPenaltyRatio *
        law.correctedGammaTail alpha (law.correctedAnchor alpha w i) ≤
      law.correctedPotentialWeight alpha w i / alpha := by
  have htail := law.correctedGammaTail_mul_penaltyRatio_le_gamma_div
    halpha (law.correctedAnchor alpha w i)
  have hanchor := law.correctedGammaWeight_anchor_le_correctedPotentialWeight
    (le_of_lt halpha) w hw hmono i
  calc
    law.correctedPenaltyRatio *
        law.correctedGammaTail alpha (law.correctedAnchor alpha w i) =
      law.correctedGammaTail alpha (law.correctedAnchor alpha w i) *
        law.correctedPenaltyRatio := by ring
    _ ≤ law.correctedGammaWeight alpha (law.correctedAnchor alpha w i) / alpha :=
      htail
    _ ≤ law.correctedPotentialWeight alpha w i / alpha := by
      exact (div_le_div_iff_of_pos_right halpha).2 hanchor

/--
Drift-ready right-loss estimate in singleton-rate units.

The Stage-77 conditional right-loss proxy is first charged by the coordinate-event
upper rate `chi/n`.  The Stage-76 calibration rewrites the resulting product as the
singleton rate `(p_1/n)` times `rho`; the closed gamma-tail bound then leaves only
`g_i/alpha`.
-/
theorem meanFlipRate_mul_correctedRightConditionalLossProxy_le_singletonRate_weight_div
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    (law.meanRadius / (n : ℝ)) *
        law.acceptedRightConditionalLossProxy
          (acceptedLeftmostZeroEvent w x i)
          (law.correctedPotentialWeight alpha w) x
          (law.correctedAnchor alpha w i) ≤
      (law.oneBitMass / (n : ℝ)) *
        (law.correctedPotentialWeight alpha w i / alpha) := by
  let coeff : ℝ := law.secondFactorialRadiusMoment /
    (law.oneBitMass * ((n - 1 : ℕ) : ℝ))
  have hmeanRate : 0 ≤ law.meanRadius / (n : ℝ) :=
    div_nonneg law.meanRadius_nonneg (Nat.cast_nonneg n)
  have hproxy := law.acceptedLeftmostZeroEvent_correctedRightConditionalLossProxy_le_gammaTail
    hn hp1 (le_of_lt halpha) w hw hmono x i hi
  have hscaled := mul_le_mul_of_nonneg_left hproxy hmeanRate
  have hcal :
      (law.meanRadius / (n : ℝ)) * coeff =
        (law.oneBitMass / (n : ℝ)) * law.correctedPenaltyRatio := by
    simpa [coeff] using
      (law.mean_eventMass_mul_rightCoefficient_eq_singletonRate_mul_correctedPenaltyRatio
        hn hp1)
  have htail := law.correctedPenaltyRatio_mul_gammaTail_anchor_le_weight_div
    halpha w hw hmono i
  calc
    (law.meanRadius / (n : ℝ)) *
        law.acceptedRightConditionalLossProxy
          (acceptedLeftmostZeroEvent w x i)
          (law.correctedPotentialWeight alpha w) x
          (law.correctedAnchor alpha w i) ≤
      (law.meanRadius / (n : ℝ)) *
        (law.correctedGammaTail alpha (law.correctedAnchor alpha w i) * coeff) := by
          simpa [coeff] using hscaled
    _ = ((law.meanRadius / (n : ℝ)) * coeff) *
        law.correctedGammaTail alpha (law.correctedAnchor alpha w i) := by ring
    _ = ((law.oneBitMass / (n : ℝ)) * law.correctedPenaltyRatio) *
        law.correctedGammaTail alpha (law.correctedAnchor alpha w i) := by
          rw [hcal]
    _ = (law.oneBitMass / (n : ℝ)) *
        (law.correctedPenaltyRatio *
          law.correctedGammaTail alpha (law.correctedAnchor alpha w i)) := by ring
    _ ≤ (law.oneBitMass / (n : ℝ)) *
        (law.correctedPotentialWeight alpha w i / alpha) := by
          exact mul_le_mul_of_nonneg_left htail
            (div_nonneg (le_of_lt hp1) (Nat.cast_nonneg n))

end StaticUnaryUnbiasedMutation
end ECRuntime
