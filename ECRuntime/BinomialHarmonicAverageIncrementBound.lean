import ECRuntime.BinomialHarmonicAverageOneStep
import ECRuntime.BinomialHarmonicAverageStrictIncrease
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 162 -- USER-APPROVED statement; independently compiler-clean in Round 42.
A dimension-by-dimension marginal bound for the binomial harmonic mean.
This quantifies the diminishing per-dimension gain in the random-initial-stake
coupon-collector analysis; it does not require a log-series limit.
Statement frozen. This provisional public copy requires a complete promotion gate.
-/

/-- The increment of the binomially averaged harmonic cost is strictly
positive, and less than the harmonic level increment `1/(n+1)`. -/
theorem proposed_binomialHarmonicAverage_incrementBound (n : Nat) :
    0 <
      (((Finset.range (n + 2)).sum (fun k =>
        (Nat.choose (n + 1) k : Real) * harmonicReal k)) / (2 : Real) ^ (n + 1) -
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) ∧
    (((Finset.range (n + 2)).sum (fun k =>
        (Nat.choose (n + 1) k : Real) * harmonicReal k)) / (2 : Real) ^ (n + 1) -
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) <
      (1 : Real) / (n + 1 : Real) := by
  have hrec := proposed_binomialHarmonicAverage_oneStep n
  have hd : (0 : Real) < (n + 1 : Real) := by positivity
  have hterm : (0 : Real) < (1 : Real) / (2 : Real) ^ (n + 1) := by positivity
  have hdiff :
      (((Finset.range (n + 2)).sum (fun k =>
        (Nat.choose (n + 1) k : Real) * harmonicReal k)) / (2 : Real) ^ (n + 1) -
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) =
        (1 - (1 : Real) / (2 : Real) ^ (n + 1)) / (n + 1 : Real) := by
    rw [hrec]
    push_cast
    ring
  constructor
  · exact sub_pos.mpr (proposed_binomialHarmonicAverage_strictIncrease n)
  · rw [hdiff]
    have hprod :
        0 < ((1 : Real) / (2 : Real) ^ (n + 1)) * (n + 1 : Real) :=
      mul_pos hterm hd
    apply (div_lt_div_iff₀ hd hd).2
    nlinarith [hprod]

end ECRuntime
