import ECRuntime.LeadingOnesStandardRate
import Mathlib

open scoped BigOperators ENNReal
open Finset

namespace ECRuntime

/-!
# Stage 27 fix 27: closed form at the standard mutation rate

Stage 27 fix 26 is compiler verified warning/error-free.  The exact finite-`n`
LeadingOnes expectation is therefore promoted both for arbitrary `0 < p < 1` and,
through the repository-wide canonical `standardMutationRate`, for `p = 1/n` when
`n >= 2`.

This file performs the remaining algebraic presentation step.  No stochastic,
measure-theoretic, Markov, renewal, or countable-sum argument appears here.  We reduce
the finite residence sum to a finite geometric series and expose the conventional
closed form

  n(n-1)/2 * ((n/(n-1))^n - 1).

The proof is kept over `ℝ`; the already promoted exact-expectation theorem then lifts
the identity through `ENNReal.ofReal`.
-/

/-- Publication-facing real closed form for the exact uniformly initialized LeadingOnes
runtime at mutation rate `p = 1/n`.  The theorem using this definition assumes `n >= 2`. -/
noncomputable def leadingOnesStandardRateClosedForm (n : ℕ) : ℝ :=
  ((n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2) *
    (((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ^ n - 1)

/-- Finite geometric power sum indexed by `Fin n`, in multiplication form. -/
private theorem fin_sum_pow_mul_sub_one (r : ℝ) (n : ℕ) :
    (∑ i : Fin n, r ^ i.val) * (r - 1) = r ^ n - 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have hshift :
          (∑ i : Fin n, r ^ (i.succ).val) =
            r * ∑ i : Fin n, r ^ i.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [show (i.succ).val = i.val + 1 by rfl]
        rw [pow_succ]
        ring
      rw [hshift]
      simp only [Fin.val_zero, pow_zero]
      calc
        (1 + r * ∑ i : Fin n, r ^ i.val) * (r - 1) =
            (r - 1) + r * ((∑ i : Fin n, r ^ i.val) * (r - 1)) := by
          ring
        _ = (r - 1) + r * (r ^ n - 1) := by
          rw [ih]
        _ = r ^ (n + 1) - 1 := by
          rw [pow_succ]
          ring

/-- Division form of the finite geometric power sum. -/
private theorem fin_sum_pow_eq_geom (r : ℝ) (n : ℕ) (hr : r ≠ 1) :
    (∑ i : Fin n, r ^ i.val) = (r ^ n - 1) / (r - 1) := by
  rw [eq_div_iff (sub_ne_zero.mpr hr)]
  exact fin_sum_pow_mul_sub_one r n

/-- The promoted standard-rate finite residence formula simplifies to the conventional
closed expression. -/
theorem leadingOnesUniformExpectedRuntimeFormula_standardMutationRate_eq_closedForm
    {n : ℕ} (hn : 2 ≤ n) :
    leadingOnesUniformExpectedRuntimeFormula n (standardMutationRate n) =
      leadingOnesStandardRateClosedForm n := by
  let m : ℕ := n - 1
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hm_succ : m + 1 = n := by
    dsimp [m]
    omega
  have hnreal_ne : (n : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hnpos)
  have hmreal_ne : (m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hmpos)
  have hmreal_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hmpos
  have hmcast : (m : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hm_succ
  have hp : standardMutationRate n = (n : ℝ)⁻¹ := by
    simp [standardMutationRate, Nat.ne_of_gt hnpos]
  have hbase : 1 - (n : ℝ)⁻¹ = (m : ℝ) / (n : ℝ) := by
    field_simp [hnreal_ne]
    linarith
  have hratio : (n : ℝ) / (m : ℝ) = 1 + (m : ℝ)⁻¹ := by
    field_simp [hmreal_ne]
    linarith
  have hratio_ne_one : (n : ℝ) / (m : ℝ) ≠ 1 := by
    rw [hratio]
    have hminvpos : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmreal_pos
    linarith
  have hratio_sub_one :
      (n : ℝ) / (m : ℝ) - 1 = (m : ℝ)⁻¹ := by
    rw [hratio]
    ring
  have hterm (i : Fin n) :
      (standardMutationRate n *
          (1 - standardMutationRate n) ^ i.val)⁻¹ =
        (n : ℝ) * ((n : ℝ) / (m : ℝ)) ^ i.val := by
    rw [hp, hbase]
    rw [mul_inv_rev, ← inv_pow, inv_inv, inv_div]
    ring
  have hsum :
      (∑ i : Fin n,
          (standardMutationRate n *
            (1 - standardMutationRate n) ^ i.val)⁻¹) =
        (n : ℝ) * ∑ i : Fin n, ((n : ℝ) / (m : ℝ)) ^ i.val := by
    calc
      (∑ i : Fin n,
          (standardMutationRate n *
            (1 - standardMutationRate n) ^ i.val)⁻¹) =
          ∑ i : Fin n,
            (n : ℝ) * ((n : ℝ) / (m : ℝ)) ^ i.val := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hterm i
      _ = (n : ℝ) * ∑ i : Fin n, ((n : ℝ) / (m : ℝ)) ^ i.val := by
        rw [Finset.mul_sum]
  have hgeom :
      (∑ i : Fin n, ((n : ℝ) / (m : ℝ)) ^ i.val) =
        ((((n : ℝ) / (m : ℝ)) ^ n - 1) /
          ((n : ℝ) / (m : ℝ) - 1)) :=
    fin_sum_pow_eq_geom ((n : ℝ) / (m : ℝ)) n hratio_ne_one
  have hgeom' :
      (∑ i : Fin n, ((n : ℝ) / (m : ℝ)) ^ i.val) =
        (m : ℝ) * ((((n : ℝ) / (m : ℝ)) ^ n) - 1) := by
    rw [hgeom, hratio_sub_one]
    calc
      ((((n : ℝ) / (m : ℝ)) ^ n) - 1) / (m : ℝ)⁻¹ =
          ((((n : ℝ) / (m : ℝ)) ^ n) - 1) * ((m : ℝ)⁻¹)⁻¹ :=
        div_eq_mul_inv _ _
      _ = ((((n : ℝ) / (m : ℝ)) ^ n) - 1) * (m : ℝ) := by
        rw [inv_inv]
      _ = (m : ℝ) * ((((n : ℝ) / (m : ℝ)) ^ n) - 1) := by
        ring
  have hclosed :
      leadingOnesUniformExpectedRuntimeFormula n (standardMutationRate n) =
        ((n : ℝ) * (m : ℝ) / 2) *
          (((n : ℝ) / (m : ℝ)) ^ n - 1) := by
    rw [leadingOnesUniformExpectedRuntimeFormula_eq]
    rw [hsum, hgeom']
    ring
  simpa [leadingOnesStandardRateClosedForm, m] using hclosed

/-- Exact uniformly initialized LeadingOnes expectation at `p = 1/n` in conventional
closed form. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (standardMutationRate n)
        (standardMutationRate_pos (by omega)).le
        (standardMutationRate_lt_one hn).le =
      ENNReal.ofReal (leadingOnesStandardRateClosedForm n) := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_formula hn]
  rw [leadingOnesUniformExpectedRuntimeFormula_standardMutationRate_eq_closedForm hn]

/-- Compatibility wrapper for the local LeadingOnes spelling of the standard rate. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_standardMutationRate_eq_closedForm
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (leadingOnesStandardMutationRate n)
        (leadingOnesStandardMutationRate_pos_of_two_le hn).le
        (leadingOnesStandardMutationRate_lt_one hn).le =
      ENNReal.ofReal (leadingOnesStandardRateClosedForm n) := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_standardMutationRate_eq_formula hn]
  rw [leadingOnesStandardMutationRate_eq_standardMutationRate (by omega)]
  rw [leadingOnesUniformExpectedRuntimeFormula_standardMutationRate_eq_closedForm hn]

end ECRuntime
