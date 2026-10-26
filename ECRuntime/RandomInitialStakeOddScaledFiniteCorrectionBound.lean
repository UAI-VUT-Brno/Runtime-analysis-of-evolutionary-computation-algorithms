import ECRuntime.RandomInitialStakeSharpEvenSandwich
import ECRuntime.RandomInitialStakeOddScaledTailBridge
import Mathlib

namespace ECRuntime

/-!
Stage 205: new, unapproved candidate for Doerr--Doerr. This is a finite
odd-parity error bound, not a new assumption about the algorithm's runtime.
Its exact positive/negative correction endpoints follow from the approved
Stage 189 sandwich and the certified Stage 182 parity identity.
-/

/-- For every positive lower index, the scaled odd harmonic correction
lies within explicit rational bounds around `+1/2`. -/
theorem proposed_randomInitialStake_oddScaledCorrection_finiteBound
    (m : Nat) (hm : 1 ≤ m) :
    (1 / 2 : Real) - 1 / (4 * (m : Real)) ≤
      (((2 * m + 1 : Nat) : Real) *
        (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) ∧
    (((2 * m + 1 : Nat) : Real) *
        (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) ≤
      (1 / 2 : Real) + 1 / (4 * (((m + 1 : Nat) : Real))) := by
  obtain ⟨hl, hu⟩ := proposed_randomInitialStake_evenTail_sharpSandwich m hm
  have hp : (0 : Real) < (m : Real) := by
    exact_mod_cast (by omega : 0 < m)
  have hsp : (0 : Real) < (((m + 1 : Nat) : Real)) := by positivity
  have hcast : (((2 * m + 1 : Nat) : Real)) = 2 * (m : Real) + 1 := by
    push_cast
    ring
  have hscp : (((m + 1 : Nat) : Real)) = (m : Real) + 1 := by
    push_cast
    ring
  have hlmul := mul_le_mul_of_nonneg_left hl
    (by positivity : (0 : Real) ≤ (((2 * m + 1 : Nat) : Real)))
  have humul := mul_le_mul_of_nonneg_left hu
    (by positivity : (0 : Real) ≤ (((2 * m + 1 : Nat) : Real)))
  have hlow : ((2 * (m : Real) + 1) * (-(1 / (4 * (m : Real))))) + 1 =
      (1 / 2 : Real) - 1 / (4 * (m : Real)) := by
    field_simp
    ring
  have hupp : (2 * (m : Real) + 1) *
        (-(1 / (4 * (((m + 1 : Nat) : Real))))) + 1 =
      (1 / 2 : Real) + 1 / (4 * (((m + 1 : Nat) : Real))) := by
    rw [hscp]
    have hm1 : (m : Real) + 1 ≠ 0 := by positivity
    field_simp [hm1]
    ring
  rw [proposed_randomInitialStake_oddScaledTail_evenBridge m, hcast]
  rw [hcast] at hlmul humul
  constructor <;> linarith

end ECRuntime
