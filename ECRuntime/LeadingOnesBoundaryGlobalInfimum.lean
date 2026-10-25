import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import ECRuntime.AdaptiveLeadingOnesBoundaryPerturbationCost
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: beyond fixed-level-zero optimality, the unrestricted interior
policy class has an unattained infimum: taking p_0 up to one improves the
uniform runtime, while all positive levels use reciprocal probabilities.
A full proof needs a limit argument in ENNReal, and is a separate target. -/

/-- The reference schedule is monotonically improved by increasing the
fixed positive level-zero mutation probability, with other levels fixed. -/
theorem proposed_leadingOnes_referenceRate_monotoneBase_uniformRuntime
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (base₁ base₂ : Real)
    (h₁ : 0 < base₁) (h₂ : base₁ ≤ base₂) (h₃ : base₂ < 1) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition
          (proposed_leadingOnes_referenceOptimalRate base₂))
          (leadingOnesTarget n) x) ≤
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition
          (proposed_leadingOnes_referenceOptimalRate base₁))
          (leadingOnesTarget n) x) := by
  classical
  have hbase2 : 0 < base₂ := lt_of_lt_of_le h₁ h₂
  have hInterior (base : Real) (hb0 : 0 < base) (hb1 : base < 1) :
      ∀ j : Nat, j ≤ n →
        0 < proposed_leadingOnes_referenceOptimalRate base j ∧
        proposed_leadingOnes_referenceOptimalRate base j < 1 := by
    intro j _
    by_cases hj : j = 0
    · subst j
      simpa [proposed_leadingOnes_referenceOptimalRate] using
        (show 0 < base ∧ base < 1 from ⟨hb0, hb1⟩)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      simpa only [proposed_leadingOnes_referenceOptimalRate, if_neg hj,
        leadingOnesLocallyOptimalSchedule, one_div] using
        (proposed_leadingOnesAdaptive_optimalPositiveLevelRate_strict j hjpos)
  have hExit : ∀ i : Fin n,
      proposed_leadingOnes_referenceOptimalRate base₁ i.val *
        (1 - proposed_leadingOnes_referenceOptimalRate base₁ i.val) ^ i.val ≤
      proposed_leadingOnes_referenceOptimalRate base₂ i.val *
        (1 - proposed_leadingOnes_referenceOptimalRate base₂ i.val) ^ i.val := by
    intro i
    by_cases hi : i.val = 0
    · simpa [hi, proposed_leadingOnes_referenceOptimalRate] using h₂
    · simp [proposed_leadingOnes_referenceOptimalRate, hi]
  exact proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass
    n (proposed_leadingOnes_referenceOptimalRate base₁)
      (proposed_leadingOnes_referenceOptimalRate base₂)
      (hInterior base₁ h₁ (lt_of_le_of_lt h₂ h₃))
      (hInterior base₂ hbase2 h₃) hExit

end ECRuntime
