import ECRuntime.AdaptiveLeadingOnesUniformFullRuntime
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: the genuine uniform-initial expected runtime depends only on
per-level exit probabilities, not the parameterization of the schedule. -/

/-- Interior adaptive schedules with matching exit probabilities have
identical actual uniform-start hitting-time expectations. -/
theorem proposed_leadingOnesAdaptive_uniformRuntime_invariant_exitMass
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate₁ rate₂ : Nat → Real)
    (h₁ : ∀ j : Nat, j ≤ n → 0 < rate₁ j ∧ rate₁ j < 1)
    (h₂ : ∀ j : Nat, j ≤ n → 0 < rate₂ j ∧ rate₂ j < 1)
    (hexit : ∀ i : Fin n,
      rate₁ i.val * (1 - rate₁ i.val) ^ i.val =
      rate₂ i.val * (1 - rate₂ i.val) ^ i.val) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate₁)
          (leadingOnesTarget n) x) =
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate₂)
          (leadingOnesTarget n) x) := by
  rw [proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum n rate₁ h₁,
      proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum n rate₂ h₂]
  apply Finset.sum_congr rfl
  intro i _
  rw [hexit i]

end ECRuntime
