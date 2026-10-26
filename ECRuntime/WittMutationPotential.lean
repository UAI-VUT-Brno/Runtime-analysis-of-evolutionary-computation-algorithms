import ECRuntime.WittStandardPotential
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 42: mutation-rate parameterized Witt potential

The compiler-promoted Stage 30--41 line uses Witt's refined potential at the standard
mutation rate `p = 1/n`.  The next literature target is the fixed-scale regime
`p = c/n`, whose sharp leading runtime constant is obtained from the exact singleton
rate `p (1-p)^(n-1)`.  The geometric cancellation in the standard-rate proof is not
specific to `1/n`; what it really needs is a potential base reciprocal to the one-bit
survival probability.

This module isolates that reusable finite-dimensional structure.  For arbitrary
`0 <= p < 1`, define

`base(p) = (1-p)^(-1)`

and keep the same strict-weight exponent already verified for the standard potential.
The resulting coefficient at coordinate `i` is therefore

`base(p)^(wittStandardExponent w i)`.

The module proves positivity, monotonicity, target characterization, a finite global
envelope, and the exact reciprocal survival identity.  It also proves that at
`p = 1/n` this parameterized potential is exactly the already promoted standard Witt
potential.  No drift or acceptance case analysis is generalized in this stage.
-/

/-- Geometric base reciprocal to the one-bit survival probability. -/
noncomputable def wittMutationBase (p : ℝ) : ℝ :=
  (1 - p)⁻¹

/-- Mutation-rate parameterized Witt coefficient. -/
noncomputable def wittMutationPotentialWeight {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  wittMutationBase p ^ wittStandardExponent w i

/-- Mutation-rate parameterized Witt error potential. -/
noncomputable def wittMutationLinearPotential {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  linearErrorPotential (wittMutationPotentialWeight p w) x

/-- Strictly subunit mutation probability gives positive survival probability. -/
theorem wittMutation_survival_pos {p : ℝ} (hp1 : p < 1) :
    0 < 1 - p := by
  linarith

/-- The parameterized base is positive for every `p < 1`. -/
theorem wittMutationBase_pos {p : ℝ} (hp1 : p < 1) :
    0 < wittMutationBase p := by
  unfold wittMutationBase
  exact inv_pos.mpr (wittMutation_survival_pos hp1)

/-- For `0 <= p < 1`, the parameterized base is at least one. -/
theorem one_le_wittMutationBase {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    1 ≤ wittMutationBase p := by
  have hsurvPos : 0 < 1 - p := wittMutation_survival_pos hp1
  have hsurvLe : 1 - p ≤ 1 := by linarith
  have hbaseNonneg : 0 ≤ (1 - p)⁻¹ :=
    inv_nonneg.mpr hsurvPos.le
  have hmul := mul_le_mul_of_nonneg_left hsurvLe hbaseNonneg
  have hsurvNe : 1 - p ≠ 0 := ne_of_gt hsurvPos
  unfold wittMutationBase
  rw [inv_mul_cancel₀ hsurvNe, mul_one] at hmul
  exact hmul

/-- The base is exactly reciprocal to survival. -/
theorem wittMutationBase_mul_survival {p : ℝ} (hp1 : p < 1) :
    wittMutationBase p * (1 - p) = 1 := by
  unfold wittMutationBase
  exact inv_mul_cancel₀ (ne_of_gt (wittMutation_survival_pos hp1))

/-- Reciprocal cancellation lifts exactly to every natural power. -/
theorem wittMutationBase_pow_mul_survival_pow
    {p : ℝ} (hp1 : p < 1) (k : ℕ) :
    wittMutationBase p ^ k * (1 - p) ^ k = 1 := by
  rw [← mul_pow, wittMutationBase_mul_survival hp1]
  simp

/-- Equal objective coefficients receive equal parameterized Witt coefficients. -/
theorem wittMutationPotentialWeight_eq_of_weight_eq {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) {i j : Fin n} (hij : w i = w j) :
    wittMutationPotentialWeight p w i = wittMutationPotentialWeight p w j := by
  unfold wittMutationPotentialWeight
  rw [wittStandardExponent_eq_of_weight_eq w hij]

/-- Parameterized Witt coefficients are monotone in the objective coefficients. -/
theorem wittMutationPotentialWeight_mono_of_weight_le {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) {i j : Fin n} (hij : w i ≤ w j) :
    wittMutationPotentialWeight p w i ≤ wittMutationPotentialWeight p w j := by
  unfold wittMutationPotentialWeight
  exact (pow_right_mono₀ (one_le_wittMutationBase hp0 hp1))
    (wittStandardExponent_mono_of_weight_le w hij)

/-- Ordered objectives give nonincreasing parameterized Witt coefficients. -/
theorem wittMutationPotentialWeight_nonincreasing {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : NonincreasingLinearWeights w)
    {i j : Fin n} (hij : i.val ≤ j.val) :
    wittMutationPotentialWeight p w j ≤ wittMutationPotentialWeight p w i := by
  exact wittMutationPotentialWeight_mono_of_weight_le hp0 hp1 w (hw i j hij)

/-- Every parameterized Witt coefficient is at least one. -/
theorem one_le_wittMutationPotentialWeight {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (i : Fin n) :
    1 ≤ wittMutationPotentialWeight p w i := by
  unfold wittMutationPotentialWeight
  exact one_le_pow₀ (one_le_wittMutationBase hp0 hp1)

/-- Every parameterized Witt coefficient is strictly positive. -/
theorem wittMutationPotentialWeight_pos {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (i : Fin n) :
    0 < wittMutationPotentialWeight p w i := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_wittMutationPotentialWeight hp0 hp1 w i)

/-- Every coefficient lies below the full geometric envelope. -/
theorem wittMutationPotentialWeight_le_fullPower {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (i : Fin n) :
    wittMutationPotentialWeight p w i ≤ wittMutationBase p ^ (n - 1) := by
  unfold wittMutationPotentialWeight
  exact (pow_right_mono₀ (one_le_wittMutationBase hp0 hp1))
    (wittStandardExponent_le_pred w i)

/-- The parameterized Witt potential is nonnegative. -/
theorem wittMutationLinearPotential_nonneg {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) :
    0 ≤ wittMutationLinearPotential p w x := by
  unfold wittMutationLinearPotential
  exact linearErrorPotential_nonneg
    (wittMutationPotentialWeight p w)
    (fun i => (wittMutationPotentialWeight_pos hp0 hp1 w i).le) x

/-- The parameterized Witt potential vanishes at the all-ones optimum. -/
@[simp] theorem wittMutationLinearPotential_allOnes {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) :
    wittMutationLinearPotential p w (allOnes n) = 0 := by
  simp [wittMutationLinearPotential]

/-- Hamming error lower-bounds the parameterized Witt potential. -/
theorem zeroCount_le_wittMutationLinearPotential {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) :
    (zeroCount x : ℝ) ≤ wittMutationLinearPotential p w x := by
  unfold wittMutationLinearPotential
  exact zeroCount_le_linearErrorPotential
    (wittMutationPotentialWeight p w)
    (one_le_wittMutationPotentialWeight hp0 hp1 w) x

/-- The parameterized Witt potential is bounded by `n` times the full geometric envelope. -/
theorem wittMutationLinearPotential_le_n_mul_fullPower {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential p w x ≤
      (n : ℝ) * wittMutationBase p ^ (n - 1) := by
  unfold wittMutationLinearPotential linearErrorPotential
  have hfullNonneg : 0 ≤ wittMutationBase p ^ (n - 1) :=
    (pow_nonneg (wittMutationBase_pos hp1).le _)
  calc
    (∑ i : Fin n,
        wittMutationPotentialWeight p w i * bitValueReal (!(x i))) ≤
      ∑ _i : Fin n, wittMutationBase p ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        cases hxi : x i <;>
          simp [bitValueReal,
            wittMutationPotentialWeight_le_fullPower hp0 hp1 w i,
            hfullNonneg]
    _ = (n : ℝ) * wittMutationBase p ^ (n - 1) := by
      simp [nsmul_eq_mul]

/-- The parameterized potential vanishes exactly at the all-ones optimum. -/
theorem wittMutationLinearPotential_eq_zero_iff {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential p w x = 0 ↔ x = allOnes n := by
  constructor
  · intro hx
    have hzreal : (zeroCount x : ℝ) ≤ 0 := by
      have hzero := zeroCount_le_wittMutationLinearPotential hp0 hp1 w x
      simpa [hx] using hzero
    have hzle : zeroCount x ≤ 0 := by
      exact_mod_cast hzreal
    have hz : zeroCount x = 0 := by omega
    exact (zeroCount_eq_zero_iff_allOnes x).mp hz
  · intro hx
    subst x
    exact wittMutationLinearPotential_allOnes p w

/-- Every non-optimal state has parameterized Witt potential at least one. -/
theorem one_le_wittMutationLinearPotential_of_ne_allOnes {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) (hx : x ≠ allOnes n) :
    1 ≤ wittMutationLinearPotential p w x := by
  have hz : zeroCount x ≠ 0 := by
    intro hz0
    exact hx ((zeroCount_eq_zero_iff_allOnes x).mp hz0)
  have honeNat : 1 ≤ zeroCount x := Nat.one_le_iff_ne_zero.mpr hz
  have honeReal : (1 : ℝ) ≤ (zeroCount x : ℝ) := by
    exact_mod_cast honeNat
  exact honeReal.trans (zeroCount_le_wittMutationLinearPotential hp0 hp1 w x)

/-- On equal-weight objectives, every parameterized Witt coefficient is one. -/
theorem wittMutationPotentialWeight_eq_one_of_all_equal {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hEq : ∀ i j, w i = w j) (i : Fin n) :
    wittMutationPotentialWeight p w i = 1 := by
  simp [wittMutationPotentialWeight,
    wittStandardExponent_eq_zero_of_all_equal w hEq i]

/-- On equal-weight objectives, the parameterized potential is exactly Hamming error. -/
theorem wittMutationLinearPotential_eq_zeroCount_of_all_equal {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hEq : ∀ i j, w i = w j) (x : BitString n) :
    wittMutationLinearPotential p w x = (zeroCount x : ℝ) := by
  rw [zeroCount_cast_eq_sum_bitValueReal_not]
  unfold wittMutationLinearPotential linearErrorPotential
  apply Finset.sum_congr rfl
  intro i hi
  rw [wittMutationPotentialWeight_eq_one_of_all_equal p w hEq i]
  ring

/-! ## Recovery of the compiler-promoted standard-rate potential -/

/-- At `p=1/n`, the parameterized reciprocal-survival base equals the Stage-30 base. -/
theorem wittMutationBase_standardMutationRate_eq_wittStandardBase
    {n : ℕ} (hn : 2 ≤ n) :
    wittMutationBase (standardMutationRate n) = wittStandardBase n := by
  have hstd := wittStandardBase_mul_standardSurvival hn
  have hnpos : 0 < n := by omega
  have hnrealPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have honeLtN : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 1 < n)
  have hrateLt : standardMutationRate n < 1 := by
    rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)]
    rw [show (n : ℝ)⁻¹ = 1 / (n : ℝ) by simp]
    exact (div_lt_one hnrealPos).2 honeLtN
  have hsurvPos : 0 < 1 - standardMutationRate n := by linarith
  have hsurvNe : 1 - standardMutationRate n ≠ 0 := ne_of_gt hsurvPos
  unfold wittMutationBase
  calc
    (1 - standardMutationRate n)⁻¹ =
        1 / (1 - standardMutationRate n) := by simp
    _ = wittStandardBase n := (div_eq_iff hsurvNe).2 hstd.symm

/-- At the standard rate, every parameterized coefficient is exactly the Stage-30 coefficient. -/
theorem wittMutationPotentialWeight_standardMutationRate_eq_wittStandardPotentialWeight
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ) (i : Fin n) :
    wittMutationPotentialWeight (standardMutationRate n) w i =
      wittStandardPotentialWeight w i := by
  unfold wittMutationPotentialWeight wittStandardPotentialWeight
  rw [wittMutationBase_standardMutationRate_eq_wittStandardBase hn]

/-- Hence the complete parameterized potential recovers the promoted standard potential exactly. -/
theorem wittMutationLinearPotential_standardMutationRate_eq_wittStandardLinearPotential
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential (standardMutationRate n) w x =
      wittStandardLinearPotential w x := by
  unfold wittMutationLinearPotential wittStandardLinearPotential
  apply congrArg (fun g : Fin n → ℝ => linearErrorPotential g x)
  funext i
  exact wittMutationPotentialWeight_standardMutationRate_eq_wittStandardPotentialWeight
    hn w i

end ECRuntime
