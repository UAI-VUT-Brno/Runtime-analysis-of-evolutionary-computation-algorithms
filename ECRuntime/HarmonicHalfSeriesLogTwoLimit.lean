import ECRuntime.RLSUniformInitialCorrectionCauchy
import Mathlib

open Filter

namespace ECRuntime

/-!
Stage 158 — USER-APPROVED CANDIDATE (Round 38).
Doerr--Doerr random initial stake: direct harmonic half-series limit.
The proof uses Mathlib's *proved* logarithmic power-series HasSum,
rather than any assumed log-series axiom. This is an independent route
to Stages 139 and 141, parallel to the finite enclosure Stage 154.
The Round 37 compiler reported a reciprocal-normalization error; Round 38 repairs it. The proof is not yet compiler-certified.
-/

private theorem stage158_range_to_Icc (n : Nat) :
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

private theorem stage158_log_half :
    Real.log (1 - (1 / 2 : Real)) = -Real.log 2 := by
  have h : (1 : Real) - 1 / 2 = (2 : Real)⁻¹ := by norm_num
  rw [h, Real.log_inv]

/-- The harmonic half-series correction converges to `log 2`.
This is the common analytic dependency of the two second-order RLS
statements; it is not a substitute for the finite Stage 154 bound. -/
theorem proposed_harmonicHalfSeries_tendsto_logTwo :
    Tendsto (fun n : Nat =>
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
      atTop (nhds (Real.log 2)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (by norm_num : |(1 / 2 : Real)| < 1)).tendsto_sum_nat
  rw [stage158_log_half] at h
  simpa only [stage158_range_to_Icc, neg_neg] using h

end ECRuntime
