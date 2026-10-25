import ECRuntime.RandomInitialStakeOddHarmonicTail
import Mathlib

namespace ECRuntime

/-!
# Stage 182 pending: exact scaled odd/even harmonic-tail bridge

Source direction: Doerr--Doerr, collecting coupons with random initial
stake. The odd-indexed scaled harmonic correction equals its even tail
at the same lower index, rescaled by 2m+1, plus exactly 1. When the
even sharp correction from Stage 176 is available, this identity will
reduce the odd case to a simple scaled-limit calculation.

This is a finite identity, not a claim that either parity asymptotic has
been certified. The new theorem statement requires human approval.
-/

/-- Raising the upper harmonic index from 2m to 2m+1 changes the
(2m+1)-scaled harmonic-log error by exactly one. -/
theorem proposed_randomInitialStake_oddScaledTail_evenBridge (m : Nat) :
    (((2 * m + 1 : Nat) : Real) *
      (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) =
    (((2 * m + 1 : Nat) : Real) *
      (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) + 1 := by
  have hsucc : harmonicReal (2 * m + 1) =
      harmonicReal (2 * m) + ((2 * m + 1 : Nat) : Real)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  rw [hsucc]
  have hne : ((2 * m + 1 : Nat) : Real) ≠ 0 := by positivity
  field_simp
  ring

end ECRuntime
