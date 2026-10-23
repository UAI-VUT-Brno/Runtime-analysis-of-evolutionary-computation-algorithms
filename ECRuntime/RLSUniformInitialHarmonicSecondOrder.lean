import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.RLSRandomStart
import ECRuntime.RLSUniformInitialCorrectionEnvelope
import ECRuntime.RLSUniformInitialCorrectionCauchy
import Mathlib

open scoped BigOperators
open Filter
namespace ECRuntime

/-!
Stage 139 — USER-APPROVED theorem statement, active proof candidate.
Doerr--Doerr (2013), collecting coupons with random initial stake.
The second-order harmonic correction follows from the Stage 138 finite
identity and the classical real-power series for log 2. It deliberately
avoids a separate formalization of the Euler--Mascheroni constant.
-/

/-- A finite geometric-series majorant for the correction. The
factor 1/j makes this no larger than the corresponding powers of 1/2.
Bounding the residual tail and identifying the infinite sum with
log 2 are the remaining analytic steps. -/
private theorem stage139_correction_le_geometric (n : Nat) :
    (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤
    (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / (2 : Real) ^ j) := by
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (1 : Real) ≤ (j : Real) := by
    exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hp : (0 : Real) < (2 : Real) ^ j := by positivity
  have hden : (0 : Real) < (j : Real) * (2 : Real) ^ j :=
    mul_pos (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hj1) hp
  have hmul := mul_le_mul_of_nonneg_right hj1 (le_of_lt hp)
  exact (div_le_div_iff₀ hden hp).2 (by simpa only [one_mul] using hmul)

/-- The finite corrections form a nondecreasing sequence. This is
independent of the exact binomial transform and requires no logarithmic
series theorem. -/
private theorem stage139_correction_monotone :
    Monotone (fun n : Nat =>
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j))) := by
  intro m n hmn
  have hsubset : Finset.Icc 1 m ⊆ Finset.Icc 1 n := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hj'.1, hj'.2.trans hmn⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro j hjBig hjSmall
  positivity

/-- Boundedness of the same partial sums, using the separate Stage 143
finite estimate that was independently compiler-clean in Round 24.
The identification of their limit with `log 2` remains to be proved. -/
private theorem stage139_correction_bounded (n : Nat) :
    (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ 1 := by
  have h := (proposed_rlsUniformInitial_harmonicCorrection_geometricEnvelope n).2
  have hpow : 0 ≤ (1 : Real) / (2 : Real) ^ n := by positivity
  linarith

/-- The promoted finite Cauchy modulus controls the absolute error
between any two correction partial sums. This prepares the existence
part of the analytic limit; identifying its value with `log 2` is still
an independent obligation. -/
private theorem stage139_absolute_cauchy_rate
    (n m : Nat) (hnm : n ≤ m) :
    |(Finset.Icc 1 m).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) -
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j))| ≤
        (1 : Real) / (2 : Real) ^ n := by
  have h :=
    proposed_rlsUniformInitial_harmonicCorrection_cauchyModulus n m hnm
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The pure geometric majorant has a vanishing tail. This is a
standard geometric-series limit; the remaining analytic task is to
identify the harmonic correction's limit specifically with `log 2`. -/
private theorem stage139_geometric_tail_tendsto_zero :
    Tendsto (fun n : Nat => (1 : Real) / (2 : Real) ^ n)
      atTop (nhds (0 : Real)) := by
  have hpow : Tendsto (fun n : Nat => ((1 / 2 : Real) ^ n))
      atTop (nhds (0 : Real)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [one_div, inv_pow] using hpow

/-- A finite log-two enclosure would finish the correction-series
limit. This analytic reduction is proved without using any unverified
public theorem or importing an incomplete candidate. -/
private theorem stage139_logSeries_of_finiteEnclosure
    (hbound : ∀ n : Nat,
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ Real.log 2 ∧
      Real.log 2 ≤
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) +
        (1 : Real) / (2 : Real) ^ n) :
    Tendsto (fun n : Nat => (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2)) := by
  have herror : Tendsto (fun n : Nat => Real.log 2 -
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (0 : Real)) := by
    apply squeeze_zero
    · intro n
      exact sub_nonneg.mpr (hbound n).1
    · intro n
      apply (sub_le_iff_le_add).2
      simpa only [add_comm] using (hbound n).2
    · exact stage139_geometric_tail_tendsto_zero
  have h : Tendsto (fun n : Nat => Real.log 2 - (Real.log 2 -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))))
      atTop (nhds (Real.log 2 - 0)) :=
    tendsto_const_nhds.sub herror
  convert h using 1
  · funext n
    ring
  · ring

/-- The only non-finite ingredients needed for the second-order
statement are (i) the Stage 138 exact identity and (ii) identification of
the finite correction series with log 2. With those *as hypotheses*, the
limit follows from elementary continuity; this lemma introduces no axiom. -/
private theorem stage139_secondOrder_of_finiteIdentity_and_logSeries
    (hclosed : ∀ n : Nat,
      ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n =
        harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
    (hlog : Tendsto
      (fun n : Nat => (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2))) :
    Tendsto
      (fun n : Nat =>
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
          harmonicReal n)
      atTop (nhds (- Real.log 2)) := by
  have hneg := hlog.neg
  apply hneg.congr'
  filter_upwards [] with n
  rw [hclosed n]
  ring

/-- A finite log-two enclosure immediately gives a quantitative
second-order error estimate for the binomially averaged harmonic runtime.
The approximation is CONDITIONAL on the still-open Stage 154 enclosure;
this theorem does not smuggle that assertion into the public library. -/
private theorem stage139_finite_secondOrder_error_of_enclosure
    (n : Nat)
    (hbound :
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ Real.log 2 ∧
      Real.log 2 ≤
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) +
          (1 : Real) / (2 : Real) ^ n) :
    0 ≤ (((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
          harmonicReal n) + Real.log 2 ∧
    (((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
          harmonicReal n) + Real.log 2 ≤
      (1 : Real) / (2 : Real) ^ n := by
  rw [proposed_binomialHarmonicAverage_closedForm n]
  constructor <;> linarith [hbound.1, hbound.2]

/-! The following proved-library log-series path is independent of
Stage 154's stronger finite enclosure. It remains entirely nonpublic
until the Lean candidate compiler accepts every step. -/
private theorem stage139_range_to_Icc (n : Nat) :
    (Finset.range n).sum (fun k =>
        (1 / 2 : Real) ^ (k + 1) / ((k : Real) + 1)) =
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hout : n + 1 ∉ Finset.Icc 1 n := by simp
      have hIcc : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [Finset.sum_range_succ, hIcc, Finset.sum_insert hout, ih]
      have hterm :
          (1 / 2 : Real) ^ (n + 1) / ((n : Real) + 1) =
            (1 : Real) / (((n + 1 : Nat) : Real) * (2 : Real) ^ (n + 1)) := by
        -- Force both presentations of the half-base into the same field
        -- expression before normalizing the remaining products.
        have hhalf : (1 / 2 : Real) = (2 : Real)⁻¹ := by norm_num
        rw [hhalf]
        push_cast
        simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
      rw [hterm]
      ring

private theorem stage139_log_half :
    Real.log (1 - (1 / 2 : Real)) = -Real.log 2 := by
  have h : (1 : Real) - 1 / 2 = (2 : Real)⁻¹ := by norm_num
  rw [h, Real.log_inv]

private theorem stage139_logSeries_tendsto :
    Tendsto (fun n : Nat =>
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (by norm_num : |(1 / 2 : Real)| < 1)).tendsto_sum_nat
  rw [stage139_log_half] at h
  simpa only [stage139_range_to_Icc, neg_neg] using h


/-- The binomially averaged initial harmonic cost differs from H_n
asymptotically by minus log 2. -/
theorem proposed_rlsUniformInitial_harmonic_secondOrderCorrection :
    Tendsto
      (fun n : Nat =>
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
          harmonicReal n)
      atTop (nhds (- Real.log 2)) := by
  -- The finite ingredient is the compiler-clean Stage 138 theorem.
  -- The analytic step is supplied by Mathlib's proved logarithmic HasSum.
  have hlog : Tendsto
      (fun n : Nat => (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2)) := by
    exact stage139_logSeries_tendsto
  exact stage139_secondOrder_of_finiteIdentity_and_logSeries
    proposed_binomialHarmonicAverage_closedForm hlog

end ECRuntime
