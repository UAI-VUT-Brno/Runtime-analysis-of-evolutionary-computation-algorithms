import ECRuntime.BinomialHarmonicAverageOneStep
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 160 — USER-APPROVED statement, independently compiler-clean in Round 39.
This is a strict monotonicity consequence of the exact Stage 159 finite
random-initial-stake harmonic recurrence. It adds no asymptotic assumptions.
The standalone proof was compiler-clean; this provisional public module
requires a complete promotion gate in Round 40.
-/

private theorem stage160_one_le_two_pow (n : Nat) :
    (1 : Real) ≤ (2 : Real) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      nlinarith

/-- The mean harmonic number of a Binomial(n, 1/2) random variable strictly
increases with the number of coordinates. -/
theorem proposed_binomialHarmonicAverage_strictIncrease (n : Nat) :
    ((Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n <
    ((Finset.range (n + 2)).sum (fun k =>
      (Nat.choose (n + 1) k : Real) * harmonicReal k)) / (2 : Real) ^ (n + 1) := by
  have hpow : (2 : Real) ≤ (2 : Real) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [stage160_one_le_two_pow n]
  have hpowpos : (0 : Real) < (2 : Real) ^ (n + 1) := by positivity
  have hsmall : (1 : Real) / (2 : Real) ^ (n + 1) < 1 := by
    apply (div_lt_iff₀ hpowpos).2
    linarith
  have hterm : (0 : Real) <
      ((1 : Real) - (1 : Real) / (2 : Real) ^ (n + 1)) /
        (((n + 1 : Nat) : Real)) := by
    exact div_pos (sub_pos.mpr hsmall) (by positivity)
  rw [proposed_binomialHarmonicAverage_oneStep n]
  linarith

end ECRuntime
