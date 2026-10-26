import ECRuntime.RLSUniformInitialExact
import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.RLSUniformInitialCorrectionEnvelope
import Mathlib

open scoped BigOperators
open Filter

namespace ECRuntime

/-!
Stage 141 — USER-APPROVED STATEMENT; provisional public proof for a full verification gate.
A consequence of the exact random-start RLS runtime (Stage 134)
and the harmonic correction under development in Stage 139.

This states a dimension-linear correction relative to n H_n. It is not
an additive O(1) approximation, and it is not claimed compiler-proved.
Literature direction: Doerr--Doerr (2013), collecting coupons with a
random initial stake.
-/

/-- The runtime correction is exactly the binomial-harmonic correction
for every positive dimension. This finite reduction is independent of any
asymptotic series theorem. -/
private theorem stage141_runtime_reduction (n : Nat) (hn : 0 < n) :
    (((Finset.univ.sum (fun x : BitString n =>
      (runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness (fun _ : Fin n => (1 : Real))))
        ({allOnes n} : Set (BitString n)) x).toReal)) /
      (2 : Real) ^ n) / (n : Real)) - harmonicReal n =
    ((Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
      harmonicReal n := by
  have hw : PositiveLinearWeights (fun _ : Fin n => (1 : Real)) := by
    intro i
    norm_num
  have heq := proposed_rlsLinear_uniformInitial_runtimeAverage hn
    (fun _ : Fin n => (1 : Real)) hw
  have hn0 : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hp : (2 : Real) ^ n ≠ 0 := by positivity
  rw [heq]
  field_simp [hn0, hp]

/-- The finite Stage 138 transform identifies the exact, signed
correction to the binomial harmonic average. In conjunction with the
certified Stage 134 runtime reduction, the only missing ingredient for
the second-order runtime theorem is the log-two series limit. -/
private theorem stage141_finite_harmonic_correction (n : Nat) :
    ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
      harmonicReal n =
    - (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
  rw [proposed_binomialHarmonicAverage_closedForm n]
  ring

/-- A compiler-checkable finite witness that the normalized runtime
correction lies in [-1,0] for every positive dimension.  This has no
`log 2` premise and does not establish the limit on its own. -/
private theorem stage141_runtime_normalized_deficit_window
    (n : Nat) (hn : 0 < n) :
    -(1 : Real) ≤
      ((((Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness (fun _ : Fin n => (1 : Real))))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n) / (n : Real)) - harmonicReal n) ∧
      ((((Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness (fun _ : Fin n => (1 : Real))))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n) / (n : Real)) - harmonicReal n) ≤ 0 := by
  rw [stage141_runtime_reduction n hn,
    stage141_finite_harmonic_correction n]
  have henv :=
    proposed_rlsUniformInitial_harmonicCorrection_geometricEnvelope n
  have hp : (0 : Real) ≤ (1 : Real) / (2 : Real) ^ n := by positivity
  constructor <;> linarith

/-- Once the shared Stage 139 harmonic second-order theorem has
been proved, the full RLS result follows using only the certified finite
runtime reduction. This implication introduces no analytic assumption
beyond the explicit `h139` hypothesis. -/
private theorem stage141_runtimeSecondOrder_of_harmonicSecondOrder
    (h139 : Tendsto
      (fun n : Nat =>
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
          harmonicReal n)
      atTop (nhds (- Real.log 2))) :
    Tendsto
      (fun n : Nat =>
        if hn : 0 < n then
          ((Finset.univ.sum (fun x : BitString n =>
            (runtimeSup
              ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
                (linearFitness (fun _ : Fin n => (1 : Real))))
              ({allOnes n} : Set (BitString n)) x).toReal) /
              (2 : Real) ^ n)) / (n : Real) - harmonicReal n
        else 0)
      atTop (nhds (- Real.log 2)) := by
  apply h139.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
  simp only [dif_pos hn]
  exact (stage141_runtime_reduction n hn).symm

/-- The finite runtime normalization is within 2^(-n) of its
second-order limiting value, PROVIDED the Stage 154 finite log-two
enclosure has been established. This is a quantitative consequence, not
a proof of the unresolved enclosure. -/
private theorem stage141_runtime_secondOrder_error_of_enclosure
    (n : Nat) (hn : 0 < n)
    (hbound :
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ Real.log 2 ∧
      Real.log 2 ≤
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) +
          (1 : Real) / (2 : Real) ^ n) :
    0 ≤
      ((((Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness (fun _ : Fin n => (1 : Real))))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n) / (n : Real)) - harmonicReal n) + Real.log 2 ∧
    ((((Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness (fun _ : Fin n => (1 : Real))))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n) / (n : Real)) - harmonicReal n) + Real.log 2 ≤
      (1 : Real) / (2 : Real) ^ n := by
  rw [stage141_runtime_reduction n hn,
    stage141_finite_harmonic_correction n]
  constructor <;> linarith [hbound.1, hbound.2]

/-! The following proved-library log-series path is independent of
Stage 154's stronger finite enclosure. It remains entirely nonpublic
until the Lean candidate compiler accepts every step. -/
private theorem stage141_range_to_Icc (n : Nat) :
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

private theorem stage141_log_half :
    Real.log (1 - (1 / 2 : Real)) = -Real.log 2 := by
  have h : (1 : Real) - 1 / 2 = (2 : Real)⁻¹ := by norm_num
  rw [h, Real.log_inv]

private theorem stage141_logSeries_tendsto :
    Tendsto (fun n : Nat =>
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (by norm_num : |(1 / 2 : Real)| < 1)).tendsto_sum_nat
  rw [stage141_log_half] at h
  simpa only [stage141_range_to_Icc, neg_neg] using h


/-- The uniform-start expected runtime minus n H_n, after dividing
by n, tends to -log 2 for RLS on OneMax, and hence on every positive
linear function. We state it for the canonical all-one weights. -/
theorem proposed_rlsLinear_uniformStart_runtime_secondOrder :
    Tendsto
      (fun n : Nat =>
        if hn : 0 < n then
          ((Finset.univ.sum (fun x : BitString n =>
            (runtimeSup
              ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
                (linearFitness (fun _ : Fin n => (1 : Real))))
              ({allOnes n} : Set (BitString n)) x).toReal) /
              (2 : Real) ^ n)) / (n : Real) - harmonicReal n
        else 0)
      atTop (nhds (- Real.log 2)) := by
  -- Standalone nonpublic log-series argument while Stage 139 awaits promotion.
  have h139 : Tendsto
      (fun n : Nat =>
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n -
          harmonicReal n)
      atTop (nhds (- Real.log 2)) := by
    have hneg := stage141_logSeries_tendsto.neg
    apply hneg.congr'
    filter_upwards [] with n
    rw [proposed_binomialHarmonicAverage_closedForm n]
    ring
  exact stage141_runtimeSecondOrder_of_harmonicSecondOrder h139

end ECRuntime
