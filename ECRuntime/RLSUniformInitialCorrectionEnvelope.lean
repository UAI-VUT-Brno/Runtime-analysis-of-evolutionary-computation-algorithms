import ECRuntime.RLSRandomStart
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 143 — promoted after successful Round 25 eight-gate verification.
Source direction: Doerr--Doerr (2013), collecting coupons with random
initial stake. This is a finite-dimensional bound for the correction in
Stages 137--139. Unlike the exact Stage 138 binomial transform, the
bound requires only elementary algebra and a geometric series.
- No theorem from an unapproved candidate is imported.
- The proof compiled independently without warnings in Round 24; the
  Round 25 full gate and non-vacuity checks passed; compiler guards are
  pinned in ECRuntimeTest.Round25PromotionPins.
-/

/-- The finite geometric half-series equals `1 - 2^(-n)` for all n,
including the empty sum at n=0. -/
private theorem stage143_half_geometric_sum (n : Nat) :
    (Finset.Icc 1 n).sum (fun j => (1 : Real) / (2 : Real) ^ j) =
      1 - (1 : Real) / (2 : Real) ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hout : n + 1 ∉ Finset.Icc 1 n := by simp
      have hIcc : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert hout, ih, pow_succ]
      have hpow : (2 : Real) ^ n ≠ 0 := by positivity
      field_simp [hpow]
      ring

/-- The finite correction that appears in the uniform-start RLS runtime
is nonnegative and lies below the explicit geometric envelope
`1 - 2^(-n)`. In particular, the correction is uniformly bounded by 1.
The exact finite binomial identity of Stage 138 is not assumed here. -/
theorem proposed_rlsUniformInitial_harmonicCorrection_geometricEnvelope
    (n : Nat) :
    0 ≤ (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ∧
    (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤
      1 - (1 : Real) / (2 : Real) ^ n := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    positivity
  · calc
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
      _ = 1 - (1 : Real) / (2 : Real) ^ n :=
        stage143_half_geometric_sum n

end ECRuntime
