import ECRuntime.AdaptiveLeadingOnesScheduleExitComparison
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: a one-coordinate policy-improvement rule for genuine expected
optimization time, obtained from the certified exact-runtime comparison. -/

/-- Improving the mutation exit mass at one fitness level, while leaving
all other level rates fixed, cannot increase uniform expected runtime. -/
theorem proposed_leadingOnesAdaptive_oneLevelImprovement_uniformRuntime
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate₁ rate₂ : Nat → Real)
    (h₁ : ∀ j : Nat, j ≤ n → 0 < rate₁ j ∧ rate₁ j < 1)
    (h₂ : ∀ j : Nat, j ≤ n → 0 < rate₂ j ∧ rate₂ j < 1)
    (pivot : Fin n)
    (hsame : ∀ i : Fin n, i ≠ pivot → rate₁ i.val = rate₂ i.val)
    (hbetter :
      rate₁ pivot.val * (1 - rate₁ pivot.val) ^ pivot.val ≤
        rate₂ pivot.val * (1 - rate₂ pivot.val) ^ pivot.val) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate₂)
          (leadingOnesTarget n) x) ≤
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate₁)
          (leadingOnesTarget n) x) := by
  have hexit : ∀ i : Fin n,
      rate₁ i.val * (1 - rate₁ i.val) ^ i.val ≤
      rate₂ i.val * (1 - rate₂ i.val) ^ i.val := by
    intro i
    by_cases hi : i = pivot
    · simpa only [hi] using hbetter
    · rw [hsame i hi]
  exact proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass
    n rate₁ rate₂ h₁ h₂ hexit

end ECRuntime
