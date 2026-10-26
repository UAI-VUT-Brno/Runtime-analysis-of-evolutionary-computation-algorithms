import ECRuntime.StaticUnaryUnbiasedCorrectedRuntime
import ECRuntime.StaticUnaryUnbiasedCorrectedPotential
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Explicit finite-dimensional runtime envelope for corrected unary-unbiased mutation

This Stage-85 candidate turns the compiler-verified Stage-84 hitting-time
certificate into a bound expressed in the dimension and the first two
radius statistics.  The corrected calibration is

  `ρ = χ E[K(K-1)] / ((n-1) p₁²)`.

It is essential that the second **factorial** moment is retained exactly.
Nothing in this module replaces it by the square of the mean radius.  The
potential envelope is independent of the magnitude ratios of the objective
weights, thanks to suffix clipping.  The runtime bound handles the optimum
as a separate zero-potential case; it never takes the logarithm of zero.

This module is intentionally outside the promoted root until its focused
build, axiom/type evidence, and later strict integration are verified.
-/

/-- A corrected clipped coefficient is at most the largest geometric
coefficient, irrespective of the ratios between the objective weights. -/
theorem correctedPotentialWeight_le_dimension_geometric
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (i : Fin n) :
    law.correctedPotentialWeight alpha w i ≤
      law.correctedGammaBase alpha ^ (n - 1) := by
  have hbase : 1 ≤ law.correctedGammaBase alpha :=
    law.one_le_correctedGammaBase halpha
  have hbase0 : 0 ≤ law.correctedGammaBase alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans hbase
  have hi : i.val < n := i.isLt
  have hexp : n - 1 - i.val + i.val = n - 1 := by omega
  calc
    law.correctedPotentialWeight alpha w i ≤
        law.correctedGammaWeight alpha i :=
      law.correctedPotentialWeight_le_gamma alpha w hw i
    _ = law.correctedGammaBase alpha ^ (n - 1 - i.val) := rfl
    _ = law.correctedGammaBase alpha ^ (n - 1 - i.val) * 1 := by ring
    _ ≤ law.correctedGammaBase alpha ^ (n - 1 - i.val) *
          law.correctedGammaBase alpha ^ i.val :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hbase) (pow_nonneg hbase0 _)
    _ = law.correctedGammaBase alpha ^ (n - 1) := by
      rw [← pow_add, hexp]

/-- The corrected potential lies between zero and the dimension times the
largest geometric coefficient.  The upper envelope uses no objective weight
ratios, and the lower envelope uses ordered positive objective weights. -/
theorem correctedLinearPotential_le_dimension_geometric
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    0 ≤ law.correctedLinearPotential alpha w x ∧
      law.correctedLinearPotential alpha w x ≤
        (n : ℝ) * law.correctedGammaBase alpha ^ (n - 1) := by
  refine ⟨law.correctedLinearPotential_nonneg halpha w hw hmono x, ?_⟩
  have hbase0 : 0 ≤ law.correctedGammaBase alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (law.one_le_correctedGammaBase halpha)
  have hz : (zeroCount x : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast zeroCount_le x
  calc
    law.correctedLinearPotential alpha w x =
        ∑ i ∈ zeroPositions x, law.correctedPotentialWeight alpha w i := by
      rw [correctedLinearPotential, linearErrorPotential_eq_sum_zeroPositions]
    _ ≤ ∑ _i ∈ zeroPositions x, law.correctedGammaBase alpha ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact law.correctedPotentialWeight_le_dimension_geometric hn halpha w hw i
    _ = ((zeroPositions x).card : ℝ) *
          law.correctedGammaBase alpha ^ (n - 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (zeroCount x : ℝ) * law.correctedGammaBase alpha ^ (n - 1) := by
      rw [zeroPositions_card]
    _ ≤ (n : ℝ) * law.correctedGammaBase alpha ^ (n - 1) :=
      mul_le_mul_of_nonneg_right hz (pow_nonneg hbase0 _)

/-- The Stage-84 hitting-time certificate yields a dimension-dependent
runtime bound with the exact second factorial moment of the mutation radius.
The target is the all-ones optimum, and the bound holds for *every* initial
bit string, including the optimum itself. -/
theorem correctedLinearPotential_runtimeSup_le_explicit
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 1 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup (law.transition (linearFitness w))
        ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal
        (((n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) +
            alpha * law.meanRadius * law.secondFactorialRadiusMoment /
              law.oneBitMass ^ 2)) := by
  let V : BitString n → ℝ := law.correctedLinearPotential alpha w
  let δ : ℝ := (law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha)
  let B : ℝ := law.correctedGammaBase alpha
  let Q : ℝ := alpha * law.meanRadius *
    law.secondFactorialRadiusMoment / law.oneBitMass ^ 2
  let R : ℝ := (n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))
  have halpha0 : 0 ≤ alpha := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt halpha)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hp1ne : law.oneBitMass ≠ 0 := ne_of_gt hp1
  have hδ : 0 < δ :=
    law.correctedLinearPotential_multiplicativeRate_pos hn hp1 halpha
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg halpha0 law.meanRadius_nonneg)
        law.secondFactorialRadiusMoment_nonneg)
      (sq_nonneg law.oneBitMass)
  have hlogn : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hbracket : 0 ≤ 1 + Real.log (n : ℝ) + Q := by linarith
  have hrate : δ⁻¹ = R := by
    dsimp [δ, R]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hR : 0 ≤ R := by
    rw [← hrate]
    exact inv_nonneg.mpr hδ.le
  have hcert :
      runtimeSup (law.transition (linearFitness w))
          ({allOnes n} : Set (BitString n)) x ≤
        ENNReal.ofReal (multiplicativeDriftRuntime δ 1 V x) :=
    law.correctedLinearPotential_runtimeSup_le hn hp1 halpha w hw hmono x
  have hcertBound :
      multiplicativeDriftRuntime δ 1 V x ≤
        R * (1 + Real.log (n : ℝ) + Q) := by
    by_cases hxzero : V x = 0
    · have hzero : multiplicativeDriftRuntime δ 1 V x = 0 := by
        unfold multiplicativeDriftRuntime additiveDriftRuntime
        simp [multiplicativeDriftPotential, hxzero]
      rw [hzero]
      exact mul_nonneg hR hbracket
    · have hxpos : 0 < V x :=
        lt_of_le_of_ne
          (law.correctedLinearPotential_nonneg halpha0 w hw hmono x)
          (Ne.symm hxzero)
      have hbase : 1 ≤ B := law.one_le_correctedGammaBase halpha0
      have hbasepos : 0 < B := lt_of_lt_of_le zero_lt_one hbase
      have hpowne : B ^ (n - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hbasepos)
      have hVupper : V x ≤ (n : ℝ) * B ^ (n - 1) :=
        (law.correctedLinearPotential_le_dimension_geometric
          hn halpha0 w hw hmono x).2
      have hlogV : Real.log (V x) ≤
          Real.log (n : ℝ) + Q := by
        have hlogUpper := Real.log_le_log hxpos hVupper
        have hlogProduct :
            Real.log ((n : ℝ) * B ^ (n - 1)) =
              Real.log (n : ℝ) + ((n - 1 : ℕ) : ℝ) * Real.log B := by
          rw [Real.log_mul hnne hpowne, Real.log_pow]
        rw [hlogProduct] at hlogUpper
        have hlogBase : Real.log B ≤ alpha * law.correctedPenaltyRatio := by
          have hlogRaw := Real.log_le_sub_one_of_pos hbasepos
          dsimp [B, correctedGammaBase] at hlogRaw ⊢
          linarith
        have hscaled :
            ((n - 1 : ℕ) : ℝ) * Real.log B ≤
              ((n - 1 : ℕ) : ℝ) * (alpha * law.correctedPenaltyRatio) :=
          mul_le_mul_of_nonneg_left hlogBase (Nat.cast_nonneg _)
        have hpredne : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
          exact_mod_cast (show n - 1 ≠ 0 by omega)
        have hmoment :
            ((n - 1 : ℕ) : ℝ) * (alpha * law.correctedPenaltyRatio) = Q := by
          dsimp [Q, correctedPenaltyRatio]
          field_simp [hpredne, hp1ne]
        linarith
      have heq : multiplicativeDriftRuntime δ 1 V x =
          δ⁻¹ * (1 + Real.log (V x)) := by
        have hh := multiplicativeDriftRuntime_eq_log_ratio
          V δ 1 (by norm_num) x hxzero
        simpa only [div_one] using hh
      rw [heq, hrate]
      exact mul_le_mul_of_nonneg_left (by linarith) hR
  have hfinal := hcert.trans (ENNReal.ofReal_le_ofReal hcertBound)
  simpa only [R, Q] using hfinal

end StaticUnaryUnbiasedMutation
end ECRuntime
