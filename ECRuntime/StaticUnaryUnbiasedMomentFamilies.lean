import ECRuntime.StaticUnaryUnbiasedExplicitRuntime
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 86: moment-controlled runtime families and the uniform one-bit operator

This candidate specializes the Stage-85 finite expected-runtime certificate to
uniform moment assumptions and to the genuinely unary-unbiased operator that
flips exactly one uniformly chosen bit.  In contrast with independent bit
mutation, its mutation radius is identically one.

The uniform estimates preserve the *second factorial moment* rather than
substituting the square of the first moment.  Their leading factors are not
claimed to reproduce the tight theorem of Doerr--Janett--Lengler (2024).
-/

/-- A uniform first/second-factorial-moment envelope for the expected runtime.
The bounds `p₀`, `C₁`, and `C₂` may depend on a chosen family of laws, but are
fixed throughout this finite-dimensional statement. -/
theorem correctedLinearPotential_runtimeSup_le_uniform_moments
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ law.oneBitMass)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hmean : law.meanRadius ≤ C₁)
    (hsecond : law.secondFactorialRadiusMoment ≤ C₂)
    {alpha : ℝ} (halpha : 1 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup (law.transition (linearFitness w))
        ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal
        (((n : ℝ) / (p₀ * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) + alpha * C₁ * C₂ / p₀ ^ 2)) := by
  have hp₁pos : 0 < law.oneBitMass := lt_of_lt_of_le hp₀ hp₁
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hfactor : 0 < 1 - 1 / alpha := by
    have hdiv : (1 : ℝ) / alpha < 1 := by
      apply (div_lt_iff₀ halphaPos).2
      simpa using halpha
    linarith
  have halpha0 : 0 ≤ alpha := halphaPos.le
  have hden₀ : 0 < p₀ * (1 - 1 / alpha) := mul_pos hp₀ hfactor
  have hden₁ : 0 < law.oneBitMass * (1 - 1 / alpha) :=
    mul_pos hp₁pos hfactor
  have hpower : p₀ ^ 2 ≤ law.oneBitMass ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp₁)
      (add_nonneg hp₁pos.le hp₀.le)]
  have hproduct : law.meanRadius * law.secondFactorialRadiusMoment ≤ C₁ * C₂ := by
    calc
      law.meanRadius * law.secondFactorialRadiusMoment ≤
          C₁ * law.secondFactorialRadiusMoment :=
        mul_le_mul_of_nonneg_right hmean law.secondFactorialRadiusMoment_nonneg
      _ ≤ C₁ * C₂ := mul_le_mul_of_nonneg_left hsecond hC₁
  have hmoment :
      law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 ≤ C₁ * C₂ / p₀ ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hp₁pos 2) (pow_pos hp₀ 2)).2
    calc
      (law.meanRadius * law.secondFactorialRadiusMoment) * p₀ ^ 2 ≤
          (C₁ * C₂) * p₀ ^ 2 :=
        mul_le_mul_of_nonneg_right hproduct (sq_nonneg p₀)
      _ ≤ (C₁ * C₂) * law.oneBitMass ^ 2 :=
        mul_le_mul_of_nonneg_left hpower (mul_nonneg hC₁ hC₂)
  have hQ :
      alpha * law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 ≤ alpha * C₁ * C₂ / p₀ ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hmoment halpha0
    calc
      alpha * law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 =
        alpha * (law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2) := by ring
      _ ≤ alpha * (C₁ * C₂ / p₀ ^ 2) := hscaled
      _ = alpha * C₁ * C₂ / p₀ ^ 2 := by ring
  have hratio :
      (n : ℝ) / (law.oneBitMass * (1 - 1 / alpha)) ≤
        (n : ℝ) / (p₀ * (1 - 1 / alpha)) := by
    apply (div_le_div_iff₀ hden₁ hden₀).2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp₁ hfactor.le) (Nat.cast_nonneg n)
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hQ0 :
      0 ≤ alpha * law.meanRadius * law.secondFactorialRadiusMoment /
        law.oneBitMass ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg halpha0 law.meanRadius_nonneg)
      law.secondFactorialRadiusMoment_nonneg) (sq_nonneg _)
  have hbracket :
      0 ≤ 1 + Real.log (n : ℝ) +
        alpha * law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 := by linarith
  have hprefix : 0 ≤ (n : ℝ) / (p₀ * (1 - 1 / alpha)) :=
    div_nonneg (Nat.cast_nonneg n) hden₀.le
  have hreal :
      ((n : ℝ) / (law.oneBitMass * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) +
            alpha * law.meanRadius * law.secondFactorialRadiusMoment /
              law.oneBitMass ^ 2) ≤
        ((n : ℝ) / (p₀ * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) + alpha * C₁ * C₂ / p₀ ^ 2) := by
    calc
      _ ≤ ((n : ℝ) / (p₀ * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) +
            alpha * law.meanRadius * law.secondFactorialRadiusMoment /
              law.oneBitMass ^ 2) :=
        mul_le_mul_of_nonneg_right hratio hbracket
      _ ≤ ((n : ℝ) / (p₀ * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) + alpha * C₁ * C₂ / p₀ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hprefix
  exact (law.correctedLinearPotential_runtimeSup_le_explicit
    hn hp₁pos halpha w hw hmono x).trans
      (ENNReal.ofReal_le_ofReal hreal)

/-- An explicit `n (1 + log n)` envelope for every law whose one-bit mass
is uniformly positive and whose first two radius moments are uniformly
bounded. The displayed coefficient is independent of `n` whenever the
moment bounds and `alpha` are independent of `n`. -/
theorem correctedLinearPotential_runtimeSup_le_uniform_nlogn
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ law.oneBitMass)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hmean : law.meanRadius ≤ C₁)
    (hsecond : law.secondFactorialRadiusMoment ≤ C₂)
    {alpha : ℝ} (halpha : 1 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup (law.transition (linearFitness w))
        ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal
        (((1 + alpha * C₁ * C₂ / p₀ ^ 2) /
            (p₀ * (1 - 1 / alpha))) *
          (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hfactor : 0 < 1 - 1 / alpha := by
    have hdiv : (1 : ℝ) / alpha < 1 := by
      apply (div_lt_iff₀ halphaPos).2
      simpa using halpha
    linarith
  have hden : 0 < p₀ * (1 - 1 / alpha) := mul_pos hp₀ hfactor
  have hprefix : 0 ≤ (n : ℝ) / (p₀ * (1 - 1 / alpha)) :=
    div_nonneg (Nat.cast_nonneg n) hden.le
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  have hD : 0 ≤ alpha * C₁ * C₂ / p₀ ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg halphaPos.le hC₁) hC₂)
      (sq_nonneg p₀)
  have hbracket :
      1 + Real.log (n : ℝ) + alpha * C₁ * C₂ / p₀ ^ 2 ≤
        (1 + alpha * C₁ * C₂ / p₀ ^ 2) *
          (1 + Real.log (n : ℝ)) := by
    nlinarith [mul_nonneg hD hlog]
  have hreal :
      ((n : ℝ) / (p₀ * (1 - 1 / alpha))) *
          (1 + Real.log (n : ℝ) + alpha * C₁ * C₂ / p₀ ^ 2) ≤
        ((1 + alpha * C₁ * C₂ / p₀ ^ 2) /
            (p₀ * (1 - 1 / alpha))) *
          (n : ℝ) * (1 + Real.log (n : ℝ)) := by
    calc
      _ ≤ ((n : ℝ) / (p₀ * (1 - 1 / alpha))) *
          ((1 + alpha * C₁ * C₂ / p₀ ^ 2) *
            (1 + Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hbracket hprefix
      _ = _ := by ring
  exact (law.correctedLinearPotential_runtimeSup_le_uniform_moments
    hn hp₀ hp₁ hC₁ hC₂ hmean hsecond halpha w hw hmono x).trans
      (ENNReal.ofReal_le_ofReal hreal)

/-- The radius-one static unary-unbiased mutation operator: each singleton
mask receives mass `1/n`, and every other mask receives zero mass. -/
noncomputable def uniformOneBitLaw {n : ℕ} (hn : 0 < n) :
    StaticUnaryUnbiasedMutation n := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  refine
    { weight := fun mask => if mask.card = 1 then (n : ℝ)⁻¹ else 0,
      weight_nonneg := ?_,
      weight_sum := ?_,
      card_invariant := ?_ }
  · intro mask
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg n)
    · exact le_refl 0
  · have hmembership (mask : MutationMask n) :
        (mask.card = 1) ↔
          mask ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) := by
        simp
    have hsum :
        (∑ mask : MutationMask n, if mask.card = 1 then (n : ℝ)⁻¹ else 0) =
          ∑ mask ∈ Finset.powersetCard 1
            (Finset.univ : Finset (Fin n)), (n : ℝ)⁻¹ := by
      simp_rw [hmembership]
      exact Finset.sum_ite_mem_eq
        (Finset.powersetCard 1 (Finset.univ : Finset (Fin n)))
        (fun _mask : MutationMask n => (n : ℝ)⁻¹)
    have hcard :
        (Finset.powersetCard 1 (Finset.univ : Finset (Fin n))).card = n := by
      simp
    calc
      (∑ mask : MutationMask n, if mask.card = 1 then (n : ℝ)⁻¹ else 0) =
          ∑ mask ∈ Finset.powersetCard 1
            (Finset.univ : Finset (Fin n)), (n : ℝ)⁻¹ := hsum
      _ = (n : ℝ) * (n : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ = 1 := by field_simp [hn0]
  · intro mask₁ mask₂ hcard
    simp [hcard]

/-- A uniform one-bit mutation has total singleton probability exactly one. -/
theorem uniformOneBitLaw_oneBitMass {n : ℕ} (hn : 0 < n) :
    (uniformOneBitLaw hn).oneBitMass = 1 := by
  let i : Fin n := ⟨0, hn⟩
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (uniformOneBitLaw hn).oneBitMass =
        (n : ℝ) * (uniformOneBitLaw hn).weight ({i} : MutationMask n) :=
      (uniformOneBitLaw hn).oneBitMass_eq_n_mul_singleton i
    _ = (n : ℝ) * (n : ℝ)⁻¹ := by
      simp [uniformOneBitLaw]
    _ = 1 := by field_simp [hn0]

/-- The radius distribution of the uniform one-bit operator is a point mass
at radius one. -/
theorem uniformOneBitLaw_radiusMass {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (uniformOneBitLaw hn).radiusMass k = if k = 1 then 1 else 0 := by
  classical
  by_cases hk : k = 1
  · subst k
    simpa [oneBitMass] using uniformOneBitLaw_oneBitMass hn
  · simp only [if_neg hk]
    unfold radiusMass
    apply Finset.sum_eq_zero
    intro mask hmask
    have hcard : mask.card = k := (Finset.mem_powersetCard.mp hmask).2
    simp [uniformOneBitLaw, hcard, hk]

/-- The exact mean radius of the uniform one-bit law. -/
theorem uniformOneBitLaw_meanRadius {n : ℕ} (hn : 0 < n) :
    (uniformOneBitLaw hn).meanRadius = 1 := by
  unfold meanRadius
  calc
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * (uniformOneBitLaw hn).radiusMass k) =
        ∑ k ∈ Finset.range (n + 1), if k = 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [uniformOneBitLaw_radiusMass hn]
      split_ifs with h
      · subst k
        norm_num
      · simp
    _ = 1 := by
      have hmem : 1 ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (by omega)
      simp [hmem]

/-- The exact second factorial radius moment of a one-bit law is zero. -/
theorem uniformOneBitLaw_secondFactorialRadiusMoment {n : ℕ} (hn : 0 < n) :
    (uniformOneBitLaw hn).secondFactorialRadiusMoment = 0 := by
  unfold secondFactorialRadiusMoment
  apply Finset.sum_eq_zero
  intro k hk
  rw [uniformOneBitLaw_radiusMass hn]
  by_cases h : k = 1
  · subst k
    norm_num
  · simp [h]

/-- Concrete expected-runtime certificate for randomized local search with
uniform one-bit mutation and the corrected potential at slack `alpha = 2`.
This is a distinct operator from independent bit mutation. -/
theorem uniformOneBitLaw_runtimeSup_le
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    runtimeSup ((uniformOneBitLaw (show 0 < n by omega)).transition
        (linearFitness w)) ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal (2 * (n : ℝ) * (1 + Real.log (n : ℝ))) := by
  have hnpos : 0 < n := by omega
  let law : StaticUnaryUnbiasedMutation n := uniformOneBitLaw hnpos
  have hp₁ : law.oneBitMass = 1 := uniformOneBitLaw_oneBitMass hnpos
  have hmean : law.meanRadius = 1 := uniformOneBitLaw_meanRadius hnpos
  have hm₂ : law.secondFactorialRadiusMoment = 0 :=
    uniformOneBitLaw_secondFactorialRadiusMoment hnpos
  have hp₁pos : 0 < law.oneBitMass := by
    rw [hp₁]
    norm_num
  have hcert := law.correctedLinearPotential_runtimeSup_le_explicit
    hn hp₁pos (show (1 : ℝ) < 2 by norm_num) w hw hmono x
  have hhalfInv : (1 - 1 / (2 : ℝ))⁻¹ = 2 := by norm_num
  have hnum : (n : ℝ) / (1 - 1 / (2 : ℝ)) = 2 * (n : ℝ) := by
    rw [div_eq_mul_inv, hhalfInv]
    ring
  have hreal :
      ((n : ℝ) / (law.oneBitMass * (1 - 1 / (2 : ℝ)))) *
          (1 + Real.log (n : ℝ) + (2 : ℝ) * law.meanRadius *
            law.secondFactorialRadiusMoment / law.oneBitMass ^ 2) =
        2 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
    calc
      _ = ((n : ℝ) / (1 - 1 / (2 : ℝ))) * (1 + Real.log (n : ℝ)) := by
        simp [hp₁, hmean, hm₂]
      _ = 2 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by rw [hnum]
  change runtimeSup (law.transition (linearFitness w))
      ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal (2 * (n : ℝ) * (1 + Real.log (n : ℝ)))
  exact hcert.trans (ENNReal.ofReal_le_ofReal hreal.le)

end StaticUnaryUnbiasedMutation
end ECRuntime
