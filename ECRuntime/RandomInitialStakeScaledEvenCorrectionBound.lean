import ECRuntime.RandomInitialStakeSharpEvenSandwich
import Mathlib

namespace ECRuntime

/-!
Stage 203 (new, awaiting human statement approval).
A *finite*, explicitly quantified error enclosure for the scaled even
harmonic correction. It makes the order-1/m remainder useful before taking
an asymptotic limit; it does not assert a complete coupon-collector runtime.
-/

/-- The scaled even dyadic correction lies within `1/(2(m+1))` of `-1/2`. -/
theorem proposed_randomInitialStake_evenScaledCorrection_finiteBound
    (m : Nat) (hm : 1 ≤ m) :
    -(1 / 2 : Real) ≤
      (((2 * m : Nat) : Real) *
        (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) ∧
    (((2 * m : Nat) : Real) *
        (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) ≤
      -(1 / 2 : Real) + 1 / (2 * (((m + 1 : Nat) : Real))) := by
  obtain ⟨hl, hu⟩ := proposed_randomInitialStake_evenTail_sharpSandwich m hm
  have hp : (0 : Real) < (m : Real) := by exact_mod_cast (by omega : 0 < m)
  have hsp : (0 : Real) < (((m + 1 : Nat) : Real)) := by positivity
  have heq : (((2 * m : Nat) : Real)) = 2 * (m : Real) := by
    push_cast
    ring
  have hcast : (((m + 1 : Nat) : Real)) = (m : Real) + 1 := by
    push_cast
    ring
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_left hl (by positivity : (0 : Real) ≤ 2 * (m : Real))
  have h2 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : Real) ≤ 2 * (m : Real))
  have hlow : (2 * (m : Real)) * (-(1 / (4 * (m : Real)))) = -(1 / 2 : Real) := by
    field_simp
    ring
  have hupp : (2 * (m : Real)) * (-(1 / (4 * (((m + 1 : Nat) : Real))))) =
      -(1 / 2 : Real) + 1 / (2 * (((m + 1 : Nat) : Real))) := by
    rw [hcast]
    field_simp
    ring
  constructor <;> linarith

end ECRuntime
