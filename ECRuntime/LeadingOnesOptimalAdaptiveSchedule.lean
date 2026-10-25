import ECRuntime.LeadingOnesPerLevelExitOptimality
import ECRuntime.AdaptiveLeadingOnesScheduleExitComparison
import ECRuntime.AdaptiveLeadingOnesOptimalPositiveLevelRate
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-- Fix the level-zero rate (which has only a boundary minimizer), and
choose the exit-optimal rate 1/(j+1) at every positive LeadingOnes level. -/
noncomputable def proposed_leadingOnes_referenceOptimalRate (base : Real)
    (j : Nat) : Real :=
  if j = 0 then base else 1 / ((j + 1 : Nat) : Real)

/-- For fixed level-zero rate, the reciprocal positive-level schedule
minimizes the actual uniform-start expected runtime (not merely a surrogate).
The j=0 condition prevents the false assertion of an interior global
minimizer at level zero. -/
theorem proposed_leadingOnes_referenceOptimal_uniformRuntime_minimal
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (base : Real) (hbase0 : 0 < base) (hbase1 : base < 1)
    (rate : Nat → Real)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (hfirst : rate 0 = base) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup
          (leadingOnesAdaptiveTransition (proposed_leadingOnes_referenceOptimalRate base))
          (leadingOnesTarget n) x) ≤
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate)
          (leadingOnesTarget n) x) := by
  classical
  have hopt : ∀ j : Nat, j ≤ n →
      0 < proposed_leadingOnes_referenceOptimalRate base j ∧
      proposed_leadingOnes_referenceOptimalRate base j < 1 := by
    intro j _hj
    by_cases hj0 : j = 0
    · subst j
      simpa [proposed_leadingOnes_referenceOptimalRate] using
        (show 0 < base ∧ base < 1 from ⟨hbase0, hbase1⟩)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      simpa only [proposed_leadingOnes_referenceOptimalRate, if_neg hj0,
        leadingOnesLocallyOptimalSchedule, one_div] using
        (proposed_leadingOnesAdaptive_optimalPositiveLevelRate_strict j hjpos)
  have hexit : ∀ i : Fin n,
      rate i.val * (1 - rate i.val) ^ i.val ≤
      proposed_leadingOnes_referenceOptimalRate base i.val *
        (1 - proposed_leadingOnes_referenceOptimalRate base i.val) ^ i.val := by
    intro i
    by_cases hi0 : i.val = 0
    · -- The original `simp only` did not rewrite `rate 0` by `hfirst`.
      -- Normalize both sides to the same level-zero mass before reflexivity.
      simp [hi0, hfirst, proposed_leadingOnes_referenceOptimalRate]
    · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have hbound := proposed_leadingOnes_levelExitMass_le_optimal
        i.val hiPos (rate i.val)
        (hinterior i.val i.isLt.le).1.le
        (hinterior i.val i.isLt.le).2.le
      simpa only [proposed_leadingOnes_referenceOptimalRate, if_neg hi0]
        using hbound
  exact proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass
    n rate (proposed_leadingOnes_referenceOptimalRate base)
    hinterior hopt hexit

end ECRuntime
