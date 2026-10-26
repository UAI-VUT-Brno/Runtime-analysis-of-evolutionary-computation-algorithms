import ECRuntime.BinomialHarmonicAverageOneStep
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 161 — USER-APPROVED statement, provisional Round 41 public candidate.
Dimension-scaled binomial-harmonic average `n * A_n` is the exact uniform-start
one-bit RLS runtime on positive linear functions, by the already promoted
exact-runtime results. The recurrence below isolates its finite increment,
and does not require the unresolved logarithmic asymptotic arguments.
The independent Round 40 compilation was clean; full gate pending.
-/

/-- Dimension-scaled binomially averaged harmonic runtime obeys a
    finite one-step recurrence, with an explicit random-initialization term. -/
theorem proposed_binomialHarmonic_scaledRuntime_oneStep (n : Nat) :
    (((n + 1 : Nat) : Real) *
      (((Finset.range (n + 2)).sum (fun k =>
        (Nat.choose (n + 1) k : Real) * harmonicReal k)) /
        (2 : Real) ^ (n + 1))) =
      (((n + 1 : Nat) : Real) *
        (((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) /
          (2 : Real) ^ n)) +
        (1 - (1 : Real) / (2 : Real) ^ (n + 1)) := by
  rw [proposed_binomialHarmonicAverage_oneStep n, mul_add]
  have hn : (((n + 1 : Nat) : Real)) ≠ 0 := by positivity
  have hcancel (x : Real) :
      (((n + 1 : Nat) : Real)) *
        (x / (((n + 1 : Nat) : Real))) = x := by
    field_simp [hn]
  simp only [hcancel]

end ECRuntime
