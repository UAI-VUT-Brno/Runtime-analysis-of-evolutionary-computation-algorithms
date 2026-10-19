import ECRuntime.LinearPotential
import ECRuntime.MutationRateRegime
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 30: finite-dimensional sharp standard-rate linear potential

Witt's refined `p = 1/n` analysis assigns a geometric coefficient to every
coordinate.  In the paper's increasing-significance convention, equal objective
weights share the coefficient belonging to the first position of their equal-weight
block.  This repository numbers coordinates in the opposite direction (coordinate
`0` is the most important one), so the same exponent is most conveniently written as

the number of objective coefficients that are strictly smaller than the current one.

For nonincreasing objective weights this is exactly the paper's block exponent after
coordinate reversal.  The formulation has two useful formal advantages: equal
objective coefficients receive equal potential coefficients by construction, and no
auxiliary `min`/`max` choice on a finite equal-weight block is required.

This first Stage-30 slice is deliberately finite-dimensional.  It defines the sharp
standard-rate potential and proves the algebraic facts needed by the later drift case
analysis: coefficient positivity, the `e` envelope, the all-ones target
characterization, the OneMax specialization, and the reciprocal identity between the
geometric base and the standard mutation survival probability.  It does not yet claim
the sharp runtime theorem.
-/

/-- Geometric base `1 + 1/(n-1)` used in Witt's refined standard-rate potential. -/
noncomputable def wittStandardBase (n : ℕ) : ℝ :=
  1 + (((n - 1 : ℕ) : ℝ))⁻¹

/-- The Witt exponent of a coordinate: the number of strictly smaller objective weights. -/
noncomputable def wittStandardExponent {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun j => w j < w i)).card

/-- Coefficient of coordinate `i` in the refined standard-rate potential. -/
noncomputable def wittStandardPotentialWeight {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  wittStandardBase n ^ wittStandardExponent w i

/-- Refined standard-rate error potential for an ordered positive linear objective. -/
noncomputable def wittStandardLinearPotential {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  linearErrorPotential (wittStandardPotentialWeight w) x

/-- The geometric base is always at least one (including the degenerate small dimensions). -/
theorem one_le_wittStandardBase (n : ℕ) :
    1 ≤ wittStandardBase n := by
  have hinv : 0 ≤ (((n - 1 : ℕ) : ℝ))⁻¹ := by positivity
  dsimp [wittStandardBase]
  linarith

/-- In particular, the geometric base is positive. -/
theorem wittStandardBase_pos (n : ℕ) :
    0 < wittStandardBase n := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_wittStandardBase n)

/-- A coordinate itself is never counted among its strictly smaller-weight coordinates. -/
theorem wittStandardExponent_le_pred {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) :
    wittStandardExponent w i ≤ n - 1 := by
  let S : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun j => w j < w i)
  have hsubset : S ⊆ (Finset.univ : Finset (Fin n)).erase i := by
    intro j hj
    have hjlt : w j < w i := by
      simpa [S] using (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by
      intro h
      subst j
      exact (lt_irrefl (w i)) hjlt
    exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hcard := Finset.card_le_card hsubset
  simpa [wittStandardExponent, S] using hcard

/-- Raising the objective coefficient can only increase the Witt exponent. -/
theorem wittStandardExponent_mono_of_weight_le {n : ℕ}
    (w : Fin n → ℝ) {i j : Fin n} (hij : w i ≤ w j) :
    wittStandardExponent w i ≤ wittStandardExponent w j := by
  unfold wittStandardExponent
  apply Finset.card_le_card
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ k, lt_of_lt_of_le hk'.2 hij⟩

/-- Equal objective coefficients receive exactly equal Witt exponents. -/
theorem wittStandardExponent_eq_of_weight_eq {n : ℕ}
    (w : Fin n → ℝ) {i j : Fin n} (hij : w i = w j) :
    wittStandardExponent w i = wittStandardExponent w j := by
  simp [wittStandardExponent, hij]

/-- Equal objective coefficients therefore receive equal potential coefficients. -/
theorem wittStandardPotentialWeight_eq_of_weight_eq {n : ℕ}
    (w : Fin n → ℝ) {i j : Fin n} (hij : w i = w j) :
    wittStandardPotentialWeight w i = wittStandardPotentialWeight w j := by
  simp [wittStandardPotentialWeight,
    wittStandardExponent_eq_of_weight_eq w hij]

/-- The refined potential coefficients are monotone in the objective coefficients. -/
theorem wittStandardPotentialWeight_mono_of_weight_le {n : ℕ}
    (w : Fin n → ℝ) {i j : Fin n} (hij : w i ≤ w j) :
    wittStandardPotentialWeight w i ≤ wittStandardPotentialWeight w j := by
  unfold wittStandardPotentialWeight
  exact (pow_right_mono₀ (one_le_wittStandardBase n))
    (wittStandardExponent_mono_of_weight_le w hij)

/-- Under the repository ordering convention, the refined coefficients are nonincreasing too. -/
theorem wittStandardPotentialWeight_nonincreasing {n : ℕ}
    (w : Fin n → ℝ) (hw : NonincreasingLinearWeights w)
    {i j : Fin n} (hij : i.val ≤ j.val) :
    wittStandardPotentialWeight w j ≤ wittStandardPotentialWeight w i := by
  exact wittStandardPotentialWeight_mono_of_weight_le w (hw i j hij)

/-- Every refined potential coefficient is at least one. -/
theorem one_le_wittStandardPotentialWeight {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) :
    1 ≤ wittStandardPotentialWeight w i := by
  unfold wittStandardPotentialWeight
  exact one_le_pow₀ (one_le_wittStandardBase n)

/-- Every refined potential coefficient is strictly positive. -/
theorem wittStandardPotentialWeight_pos {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) :
    0 < wittStandardPotentialWeight w i := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_wittStandardPotentialWeight w i)

/-- Every coefficient is bounded by the full geometric envelope. -/
theorem wittStandardPotentialWeight_le_fullPower {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) :
    wittStandardPotentialWeight w i ≤ wittStandardBase n ^ (n - 1) := by
  unfold wittStandardPotentialWeight
  exact (pow_right_mono₀ (one_le_wittStandardBase n))
    (wittStandardExponent_le_pred w i)

/-- The full geometric envelope is at most `e`. -/
theorem wittStandardBase_fullPower_le_exp_one (n : ℕ) :
    wittStandardBase n ^ (n - 1) ≤ Real.exp 1 := by
  simpa [wittStandardBase] using
    (Real.one_add_inv_pow_le_exp (n := n - 1))

/-- Hence every refined standard-rate potential coefficient is at most `e`. -/
theorem wittStandardPotentialWeight_le_exp_one {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) :
    wittStandardPotentialWeight w i ≤ Real.exp 1 := by
  exact (wittStandardPotentialWeight_le_fullPower w i).trans
    (wittStandardBase_fullPower_le_exp_one n)

/-- The refined potential is nonnegative. -/
theorem wittStandardLinearPotential_nonneg {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) :
    0 ≤ wittStandardLinearPotential w x := by
  unfold wittStandardLinearPotential
  exact linearErrorPotential_nonneg
    (wittStandardPotentialWeight w)
    (fun i => (wittStandardPotentialWeight_pos w i).le) x

/-- The refined potential vanishes at the all-ones optimum. -/
@[simp] theorem wittStandardLinearPotential_allOnes {n : ℕ}
    (w : Fin n → ℝ) :
    wittStandardLinearPotential w (allOnes n) = 0 := by
  simp [wittStandardLinearPotential]

/-- Hamming error is a pointwise lower bound on the refined potential. -/
theorem zeroCount_le_wittStandardLinearPotential {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) :
    (zeroCount x : ℝ) ≤ wittStandardLinearPotential w x := by
  unfold wittStandardLinearPotential
  exact zeroCount_le_linearErrorPotential
    (wittStandardPotentialWeight w)
    (one_le_wittStandardPotentialWeight w) x

/-- The refined potential is globally at most `e n`. -/
theorem wittStandardLinearPotential_le_en {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) :
    wittStandardLinearPotential w x ≤ (n : ℝ) * Real.exp 1 := by
  unfold wittStandardLinearPotential linearErrorPotential
  calc
    (∑ i : Fin n, wittStandardPotentialWeight w i * bitValueReal (!(x i))) ≤
        ∑ _i : Fin n, Real.exp 1 := by
      apply Finset.sum_le_sum
      intro i hi
      cases hxi : x i <;>
        simp [bitValueReal, wittStandardPotentialWeight_le_exp_one w i,
          (Real.exp_pos (1 : ℝ)).le]
    _ = (n : ℝ) * Real.exp 1 := by
      simp [nsmul_eq_mul]

/-- The refined potential vanishes exactly at the normalized all-ones optimum. -/
theorem wittStandardLinearPotential_eq_zero_iff {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) :
    wittStandardLinearPotential w x = 0 ↔ x = allOnes n := by
  constructor
  · intro hx
    have hzreal : (zeroCount x : ℝ) ≤ 0 := by
      have h := zeroCount_le_wittStandardLinearPotential w x
      simpa [hx] using h
    have hzle : zeroCount x ≤ 0 := by
      exact_mod_cast hzreal
    have hz : zeroCount x = 0 := by omega
    exact (zeroCount_eq_zero_iff_allOnes x).mp hz
  · intro hx
    subst x
    exact wittStandardLinearPotential_allOnes w

/-- Every non-optimal search point has refined potential at least one. -/
theorem one_le_wittStandardLinearPotential_of_ne_allOnes {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (hx : x ≠ allOnes n) :
    1 ≤ wittStandardLinearPotential w x := by
  have hz : zeroCount x ≠ 0 := by
    intro hz0
    exact hx ((zeroCount_eq_zero_iff_allOnes x).mp hz0)
  have honeNat : 1 ≤ zeroCount x := Nat.one_le_iff_ne_zero.mpr hz
  have honeReal : (1 : ℝ) ≤ (zeroCount x : ℝ) := by exact_mod_cast honeNat
  exact honeReal.trans (zeroCount_le_wittStandardLinearPotential w x)

/-- If all objective coefficients agree, all Witt exponents vanish. -/
theorem wittStandardExponent_eq_zero_of_all_equal {n : ℕ}
    (w : Fin n → ℝ) (hEq : ∀ i j, w i = w j) (i : Fin n) :
    wittStandardExponent w i = 0 := by
  unfold wittStandardExponent
  have hempty :
      (Finset.univ : Finset (Fin n)).filter (fun j => w j < w i) = ∅ := by
    ext j
    simp [hEq j i]
  rw [hempty]
  simp

/-- On OneMax-type equal weights, every refined potential coefficient is exactly one. -/
theorem wittStandardPotentialWeight_eq_one_of_all_equal {n : ℕ}
    (w : Fin n → ℝ) (hEq : ∀ i j, w i = w j) (i : Fin n) :
    wittStandardPotentialWeight w i = 1 := by
  simp [wittStandardPotentialWeight,
    wittStandardExponent_eq_zero_of_all_equal w hEq i]

/-- On equal-weight objectives, the refined potential reduces exactly to Hamming error. -/
theorem wittStandardLinearPotential_eq_zeroCount_of_all_equal {n : ℕ}
    (w : Fin n → ℝ) (hEq : ∀ i j, w i = w j) (x : BitString n) :
    wittStandardLinearPotential w x = (zeroCount x : ℝ) := by
  rw [zeroCount_cast_eq_sum_bitValueReal_not]
  unfold wittStandardLinearPotential linearErrorPotential
  apply Finset.sum_congr rfl
  intro i hi
  rw [wittStandardPotentialWeight_eq_one_of_all_equal w hEq i]
  ring

/--
For `n >= 2`, the geometric base is the exact reciprocal of the probability that a
specified *other* bit survives standard mutation.
-/
theorem wittStandardBase_mul_standardSurvival {n : ℕ} (hn : 2 ≤ n) :
    wittStandardBase n * (1 - standardMutationRate n) = 1 := by
  let m : ℕ := n - 1
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hnreal_ne : (n : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hnpos)
  have hmreal_ne : (m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hmpos)
  have hm_succ : m + 1 = n := by
    dsimp [m]
    omega
  have hmcast : (m : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hm_succ
  have hp : standardMutationRate n = (n : ℝ)⁻¹ := by
    simp [standardMutationRate, Nat.ne_of_gt hnpos]
  rw [hp]
  change (1 + (m : ℝ)⁻¹) * (1 - (n : ℝ)⁻¹) = 1
  field_simp [hmreal_ne, hnreal_ne]
  nlinarith

/-- The reciprocal base/survival identity lifts exactly to every natural power. -/
theorem wittStandardBase_pow_mul_standardSurvival_pow
    {n k : ℕ} (hn : 2 ≤ n) :
    wittStandardBase n ^ k * (1 - standardMutationRate n) ^ k = 1 := by
  rw [← mul_pow, wittStandardBase_mul_standardSurvival hn]
  simp

end ECRuntime
