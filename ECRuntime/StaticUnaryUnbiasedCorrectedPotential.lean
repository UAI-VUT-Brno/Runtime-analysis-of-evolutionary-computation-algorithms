import ECRuntime.StaticUnaryUnbiasedLinearLossDecomposition
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Corrected potential calibration for static unary-unbiased linear functions

Stage 75 compiler-promoted the accepted-event `L/R` decomposition and the region-wide
right-loss bound with coefficient

`E[K(K-1)] / (p₁ (n-1))`.

The pivot event itself has mass at most `χ/n`, whereas the elementary singleton gain
has rate `p₁/n`.  Consequently the dimensionless penalty ratio that replaces the
published `χ^3 / ((n-1) p₁^2)` factor is

`ρ = χ E[K(K-1)] / ((n-1) p₁^2)`.

For a slack parameter `alpha`, the corrected geometric baseline is `1 + alpha * ρ`.
In the repository's reversed coordinate convention the baseline coefficient at index
`i` is `(1 + alpha * ρ)^(n-1-i)`.

To encode the objective clipping without a fragile reverse recursion on `Fin n`, we use
the equivalent finite suffix-min representation suggested by the recurrence:

`g_i = min_{j >= i} gamma_j * w_i / w_j`.

A concrete minimizing suffix coordinate is retained as `correctedAnchor`; this is the
reversed-convention counterpart of the literature anchor `k(i)`.  This stage establishes
the calibration identity, existence/minimality of the anchor, the geometric envelope,
and positivity/target facts.  The one-step recurrence and anchor-contact theorem are
left to the next stage, where they will be combined with the Stage-75 `L/R` split.
-/

/-- Corrected dimensionless penalty ratio
`χ E[K(K-1)] / ((n-1) p₁^2)`. -/
noncomputable def correctedPenaltyRatio {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  law.meanRadius * law.secondFactorialRadiusMoment /
    (((n - 1 : ℕ) : ℝ) * law.oneBitMass ^ 2)

/-- The corrected penalty ratio is always nonnegative. -/
theorem correctedPenaltyRatio_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.correctedPenaltyRatio := by
  unfold correctedPenaltyRatio
  exact div_nonneg
    (mul_nonneg law.meanRadius_nonneg law.secondFactorialRadiusMoment_nonneg)
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg law.oneBitMass))

/--
The exact Stage-75 event-mass/right-loss coefficient equals the singleton rate times
`correctedPenaltyRatio`.  This is the algebraic calibration replacing the published
`χ^3` factor.
-/
theorem mean_eventMass_mul_rightCoefficient_eq_singletonRate_mul_correctedPenaltyRatio
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (hn : 2 ≤ n) (hp1 : 0 < law.oneBitMass) :
    (law.meanRadius / (n : ℝ)) *
        (law.secondFactorialRadiusMoment /
          (law.oneBitMass * ((n - 1 : ℕ) : ℝ))) =
      (law.oneBitMass / (n : ℝ)) * law.correctedPenaltyRatio := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hpred0 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show n - 1 ≠ 0 by omega)
  have hp10 : law.oneBitMass ≠ 0 := ne_of_gt hp1
  unfold correctedPenaltyRatio
  field_simp [hn0, hpred0, hp10]

/-- Corrected geometric baseline `1 + alpha * rho`. -/
noncomputable def correctedGammaBase {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) : ℝ :=
  1 + alpha * law.correctedPenaltyRatio

/-- Nonnegative slack gives a geometric base at least one. -/
theorem one_le_correctedGammaBase {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha) :
    1 ≤ law.correctedGammaBase alpha := by
  unfold correctedGammaBase
  have hprod : 0 ≤ alpha * law.correctedPenaltyRatio :=
    mul_nonneg halpha law.correctedPenaltyRatio_nonneg
  linarith

/-- Reversed-index geometric baseline coefficient. -/
noncomputable def correctedGammaWeight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ) (i : Fin n) : ℝ :=
  law.correctedGammaBase alpha ^ (n - 1 - i.val)

/-- Every corrected geometric coefficient is at least one for nonnegative slack. -/
theorem one_le_correctedGammaWeight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (i : Fin n) :
    1 ≤ law.correctedGammaWeight alpha i := by
  unfold correctedGammaWeight
  exact one_le_pow₀ (law.one_le_correctedGammaBase halpha)

/-- Suffix coordinates no more important than `i` in the repository convention. -/
def CorrectedSuffixIndex {n : ℕ} (i : Fin n) :=
  {j : Fin n // i.val ≤ j.val}

instance correctedSuffixIndexNonempty {n : ℕ} (i : Fin n) :
    Nonempty (CorrectedSuffixIndex i) :=
  ⟨⟨i, le_rfl⟩⟩

/-- The suffix subtype is finite because it is a subtype of the finite coordinate type.
This explicit instance avoids relying on typeclass search unfolding `CorrectedSuffixIndex`. -/
instance correctedSuffixIndexFinite {n : ℕ} (i : Fin n) :
    Finite (CorrectedSuffixIndex i) := by
  unfold CorrectedSuffixIndex
  infer_instance

/-- Candidate clipped coefficient obtained by contacting the geometric baseline at `j`. -/
noncomputable def correctedClipCandidate {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i j : Fin n) : ℝ :=
  law.correctedGammaWeight alpha j * (w i / w j)

/-- A concrete suffix minimizer used as the corrected anchor. -/
noncomputable def correctedAnchorSubtype {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i : Fin n) : CorrectedSuffixIndex i :=
  Classical.choose
    (Finite.exists_min
      (fun j : CorrectedSuffixIndex i =>
        law.correctedClipCandidate alpha w i j.1))

/-- Reversed-convention anchor coordinate corresponding to the suffix minimizer. -/
noncomputable def correctedAnchor {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i : Fin n) : Fin n :=
  (law.correctedAnchorSubtype alpha w i).1

/-- The corrected anchor lies in the suffix beginning at `i`. -/
theorem correctedAnchor_ge {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i : Fin n) :
    i.val ≤ (law.correctedAnchor alpha w i).val := by
  exact (law.correctedAnchorSubtype alpha w i).property

/-- The chosen anchor minimizes the clipping candidate over the suffix. -/
theorem correctedAnchorSubtype_min {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i : Fin n) (j : CorrectedSuffixIndex i) :
    law.correctedClipCandidate alpha w i
        (law.correctedAnchor alpha w i) ≤
      law.correctedClipCandidate alpha w i j.1 := by
  exact
    (Classical.choose_spec
      (Finite.exists_min
        (fun q : CorrectedSuffixIndex i =>
          law.correctedClipCandidate alpha w i q.1))) j

/-- Objective-clipped corrected potential coefficient. -/
noncomputable def correctedPotentialWeight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  law.correctedClipCandidate alpha w i (law.correctedAnchor alpha w i)

/-- The clipped coefficient is below every suffix contact candidate. -/
theorem correctedPotentialWeight_le_clipCandidate {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (i j : Fin n) (hij : i.val ≤ j.val) :
    law.correctedPotentialWeight alpha w i ≤
      law.correctedClipCandidate alpha w i j := by
  unfold correctedPotentialWeight
  exact law.correctedAnchorSubtype_min alpha w i ⟨j, hij⟩

/-- In particular, clipping never exceeds the geometric baseline at the same coordinate. -/
theorem correctedPotentialWeight_le_gamma {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (i : Fin n) :
    law.correctedPotentialWeight alpha w i ≤
      law.correctedGammaWeight alpha i := by
  have hmin := law.correctedPotentialWeight_le_clipCandidate alpha w i i le_rfl
  have hwi : w i ≠ 0 := ne_of_gt (hw i)
  simpa [correctedClipCandidate, div_self hwi] using hmin

/-- Under ordered positive objective weights, every corrected clipped coefficient is at least one. -/
theorem one_le_correctedPotentialWeight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    1 ≤ law.correctedPotentialWeight alpha w i := by
  let a : Fin n := law.correctedAnchor alpha w i
  have hia : i.val ≤ a.val := by
    dsimp [a]
    exact law.correctedAnchor_ge alpha w i
  have hwa : 0 < w a := hw a
  have hweight : w a ≤ w i := hmono i a hia
  have hratio : 1 ≤ w i / w a := by
    apply (le_div_iff₀ hwa).2
    simpa using hweight
  have hgamma : 1 ≤ law.correctedGammaWeight alpha a :=
    law.one_le_correctedGammaWeight halpha a
  have hprod : (1 : ℝ) * 1 ≤
      law.correctedGammaWeight alpha a * (w i / w a) :=
    mul_le_mul hgamma hratio (by norm_num) (zero_le_one.trans hgamma)
  change 1 ≤ law.correctedClipCandidate alpha w i
    (law.correctedAnchor alpha w i)
  dsimp [correctedClipCandidate, a] at hprod ⊢
  simpa using hprod

/-- Corrected objective-clipped linear error potential. -/
noncomputable def correctedLinearPotential {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  linearErrorPotential (law.correctedPotentialWeight alpha w) x

/-- The corrected potential is nonnegative under the ordered positive-weight assumptions. -/
theorem correctedLinearPotential_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    0 ≤ law.correctedLinearPotential alpha w x := by
  unfold correctedLinearPotential
  exact linearErrorPotential_nonneg _
    (fun i => zero_le_one.trans
      (law.one_le_correctedPotentialWeight halpha w hw hmono i)) x

/-- Hamming error is bounded by the corrected potential. -/
theorem zeroCount_le_correctedLinearPotential {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    (zeroCount x : ℝ) ≤ law.correctedLinearPotential alpha w x := by
  unfold correctedLinearPotential
  exact zeroCount_le_linearErrorPotential _
    (law.one_le_correctedPotentialWeight halpha w hw hmono) x

/-- The corrected potential vanishes at the all-ones optimum. -/
@[simp] theorem correctedLinearPotential_allOnes {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (alpha : ℝ)
    (w : Fin n → ℝ) :
    law.correctedLinearPotential alpha w (allOnes n) = 0 := by
  simp [correctedLinearPotential]

/-- Under the calibrated assumptions, the corrected potential vanishes exactly at the optimum. -/
theorem correctedLinearPotential_eq_zero_iff {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    law.correctedLinearPotential alpha w x = 0 ↔ x = allOnes n := by
  constructor
  · intro hx
    have hzreal : (zeroCount x : ℝ) ≤ 0 := by
      have h := law.zeroCount_le_correctedLinearPotential halpha w hw hmono x
      simpa [hx] using h
    have hzle : zeroCount x ≤ 0 := by
      exact_mod_cast hzreal
    have hz : zeroCount x = 0 := by omega
    exact (zeroCount_eq_zero_iff_allOnes x).mp hz
  · intro hx
    subst x
    exact law.correctedLinearPotential_allOnes alpha w

end StaticUnaryUnbiasedMutation
end ECRuntime
