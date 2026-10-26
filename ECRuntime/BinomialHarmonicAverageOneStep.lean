import ECRuntime.BinomialHarmonicAverageClosedForm
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 159 — PROMOTED after the user-run Round 39 full eight-gate verification.
For the Doerr--Doerr (2013) random-initial-stake RLS/coupon-collector
branch, the binomial mean harmonic cost has an explicit one-dimension
increment. This is stronger than mere monotonicity and refines the finite
runtime description without invoking the open logarithmic limit.
The compiler-derived theorem type and axiom list are frozen in Round39PromotionPins.
-/

private theorem stage159_harmonic_succ (n : Nat) :
    harmonicReal (n + 1) =
      harmonicReal n + ((n + 1 : Nat) : Real)⁻¹ := by
  simp [harmonicReal, harmonic_succ]

private theorem stage159_correction_succ (n : Nat) :
    (Finset.Icc 1 (n + 1)).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) =
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) +
        (1 : Real) / (((n + 1 : Nat) : Real) * (2 : Real) ^ (n + 1)) := by
  have hout : n + 1 ∉ Finset.Icc 1 n := by simp
  have hIcc : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  simp only [hIcc, Finset.sum_insert hout]
  ring

/-- Exact incremental gain in the mean harmonic number of a
Binomial(n, 1/2) random initial stake. -/
theorem proposed_binomialHarmonicAverage_oneStep (n : Nat) :
    ((Finset.range (n + 2)).sum (fun k =>
      (Nat.choose (n + 1) k : Real) * harmonicReal k)) / (2 : Real) ^ (n + 1) =
    ((Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n +
      ((1 : Real) - (1 : Real) / (2 : Real) ^ (n + 1)) /
        (((n + 1 : Nat) : Real)) := by
  rw [proposed_binomialHarmonicAverage_closedForm (n + 1),
    proposed_binomialHarmonicAverage_closedForm n,
    stage159_harmonic_succ, stage159_correction_succ]
  have hn : (((n + 1 : Nat) : Real)) ≠ 0 := by positivity
  have hp : (2 : Real) ^ (n + 1) ≠ 0 := by positivity
  field_simp [hn, hp]
  ring

end ECRuntime
