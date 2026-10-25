import ECRuntime.AdaptiveLeadingOnesUniformFullRuntime
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.UnrestrictedRuntime
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: schedule optimization follows only after the genuine
full-runtime formula. This comparison uses levelwise exit *probabilities*,
not an unjustified assumption about the probabilities of visiting levels. -/

/-- An interior schedule with larger exit probability at every level has
no larger uniform expected optimization time. -/
theorem proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate₁ rate₂ : Nat → Real)
    (h₁ : ∀ j : Nat, j ≤ n → 0 < rate₁ j ∧ rate₁ j < 1)
    (h₂ : ∀ j : Nat, j ≤ n → 0 < rate₂ j ∧ rate₂ j < 1)
    (hexit : ∀ i : Fin n,
      rate₁ i.val * (1 - rate₁ i.val) ^ i.val ≤
      rate₂ i.val * (1 - rate₂ i.val) ^ i.val) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate₂)
          (leadingOnesTarget n) x) ≤
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate₁)
          (leadingOnesTarget n) x) := by
  classical
  rw [proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum n rate₂ h₂,
      proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum n rate₁ h₁]
  apply Finset.sum_le_sum
  intro i _
  have hp₁ : 0 < rate₁ i.val * (1 - rate₁ i.val) ^ i.val :=
    mul_pos (h₁ i.val i.isLt.le).1
      (pow_pos (sub_pos.mpr (h₁ i.val i.isLt.le).2) _)
  have hp₂ : 0 < rate₂ i.val * (1 - rate₂ i.val) ^ i.val :=
    mul_pos (h₂ i.val i.isLt.le).1
      (pow_pos (sub_pos.mpr (h₂ i.val i.isLt.le).2) _)
  have hinv :
      (rate₂ i.val * (1 - rate₂ i.val) ^ i.val)⁻¹ ≤
        (rate₁ i.val * (1 - rate₁ i.val) ^ i.val)⁻¹ :=
    (inv_le_inv₀ hp₂ hp₁).2 (hexit i)
  exact mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_le_ofReal hinv) (bot_le : (0 : ENNReal) ≤ 1 / 2)

end ECRuntime
