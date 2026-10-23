import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.LogTwoHarmonicCorrectionFiniteSandwich
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 163 -- USER-APPROVED statement; independently compiler-clean in Round 42.
The certified finite binomial identity combined with the compiler-clean
(but not yet full-gate promoted) log-two enclosure yields a quantitative
second-order error with no asymptotic limits and no new analytic assumptions.
The statement is frozen; its provisional public copy requires the full promotion gate.
-/

/-- For a Binomial(n,1/2) starting stake, the error in the logarithmic
correction to the expected harmonic cost is nonnegative and exponentially
small, uniformly at each finite dimension. -/
theorem proposed_binomialHarmonic_logTwoFiniteError (n : Nat) :
    0 <= Real.log 2 -
      (harmonicReal n -
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) /\
    Real.log 2 -
      (harmonicReal n -
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) <=
      (1 : Real) / (2 : Real) ^ n := by
  have hident : harmonicReal n -
      ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n =
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
    rw [proposed_binomialHarmonicAverage_closedForm n]
    ring
  rw [hident]
  have hfinite := proposed_logTwo_harmonicHalfSeries_finiteSandwich n
  constructor
  · linarith [hfinite.1]
  · linarith [hfinite.2]

end ECRuntime
