import ECRuntime.RLSRandomStart
import Mathlib

namespace ECRuntime

/-!
Stage 148 — PROMOTED after the user-supplied Round 30 official eight-gate verification.
Source direction: Doerr--Doerr (2013), random-initial-stake coupon collection.
A sharp elementary lower logarithmic envelope for harmonic numbers. The
compiler-observed theorem signature and axiom set are frozen in
`ECRuntimeTest.Round30PromotionPins`. No statement or proof change is made.
-/

/-- Logarithmic growth of `log(1+x)` is at most linear for `x ≥ 0`.
This uses `exp y ≥ 1+y` and the exp/log inverse, not numerical testing. -/
private theorem stage148_log_one_add_le (x : Real) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x := by
  have hxpos : (0 : Real) < 1 + x := by linarith
  have h := Real.add_one_le_exp (Real.log (1 + x))
  rw [Real.exp_log hxpos] at h
  linarith

/-- An elementary lower integral/log envelope for harmonic numbers,
with the correct n=0 endpoint and no asymptotic assumptions. -/
theorem proposed_harmonicReal_log_succ_le (n : Nat) :
    Real.log ((n : Real) + 1) ≤ harmonicReal n := by
  induction n with
  | zero =>
      simp [harmonicReal]
  | succ n ih =>
      have hd : 0 < (n : Real) + 1 := by positivity
      have hi : (0 : Real) ≤ 1 / ((n : Real) + 1) := by positivity
      have hfact : (n : Real) + 2 =
          ((n : Real) + 1) * (1 + 1 / ((n : Real) + 1)) := by
        field_simp [ne_of_gt hd]
        ring
      have hlog : Real.log ((n : Real) + 2) =
          Real.log ((n : Real) + 1) +
            Real.log (1 + 1 / ((n : Real) + 1)) := by
        rw [hfact, Real.log_mul (by positivity) (by positivity)]
      have hincrement := stage148_log_one_add_le _ hi
      have hsucc : harmonicReal (n + 1) =
          harmonicReal n + ((n + 1 : Nat) : Real)⁻¹ := by
        simp [harmonicReal, harmonic_succ]
      calc
        Real.log (((n + 1 : Nat) : Real) + 1) =
            Real.log ((n : Real) + 2) := by push_cast; ring
        _ = Real.log ((n : Real) + 1) +
            Real.log (1 + 1 / ((n : Real) + 1)) := hlog
        _ ≤ harmonicReal n + 1 / ((n : Real) + 1) :=
            add_le_add ih hincrement
        _ = harmonicReal (n + 1) := by
            rw [hsucc]
            push_cast
            ring

end ECRuntime
