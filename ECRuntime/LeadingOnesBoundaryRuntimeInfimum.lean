import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import ECRuntime.AdaptiveLeadingOnesUniformFullRuntime
import ECRuntime.LeadingOnesReferenceExitCostBoundaryTendsto
import ECRuntime.AdaptiveLeadingOnesOptimalPositiveLevelRate
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: the *unattained* boundary limit, not a putative interior
minimizer at the level-zero mutation probability.  The finite-cost limit
is certified in Stage 456.  The only remaining work is to link its
cost formula to the actual Bellman runtime on an eventual interior
neighborhood and to split the zero term from the filtered finite sum. -/

/-- For positive dimension the optimal reference-schedule uniform runtime
approaches the positive-level sum plus the unattained level-zero half. -/
theorem proposed_leadingOnes_referenceRuntime_boundaryInfimum
    (n : Nat) (hn : 0 < n)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)] :
    Filter.Tendsto
      (fun base : Real =>
        ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ x : BitString n,
            runtimeSup (leadingOnesAdaptiveTransition
              (proposed_leadingOnes_referenceOptimalRate base))
              (leadingOnesTarget n) x))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds ((1 / 2 : ENNReal) +
        (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val),
           (1 / 2 : ENNReal) *
              ENNReal.ofReal ((1 / ((i.val + 1 : Nat) : Real) *
                 (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹)))) := by
  classical
  let w : Fin n → ENNReal := fun i =>
    (1 / 2 : ENNReal) * ENNReal.ofReal
      ((1 / ((i.val + 1 : Nat) : Real) *
        (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹)
  let z : Fin n := ⟨0, hn⟩
  have hzmem : z ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ z
  have hfilter :
      ((Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val)) =
        (Finset.univ : Finset (Fin n)).erase z := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro hi hzero
      have heq : i.val = 0 := congrArg Fin.val hzero
      omega
    · intro hi
      have hne : i.val ≠ 0 := by
        intro hzero
        apply hi
        exact Fin.ext hzero
      exact Nat.pos_of_ne_zero hne
  have hsplit :
      (∑ i : Fin n, if i.val = 0 then (1 / 2 : ENNReal) else w i) =
        (1 / 2 : ENNReal) +
          ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val), w i := by
    calc
      (∑ i : Fin n, if i.val = 0 then (1 / 2 : ENNReal) else w i) =
          (if z.val = 0 then (1 / 2 : ENNReal) else w z) +
            ∑ i ∈ (Finset.univ : Finset (Fin n)).erase z,
              (if i.val = 0 then (1 / 2 : ENNReal) else w i) := by
                exact (Finset.add_sum_erase Finset.univ
                  (fun i : Fin n => if i.val = 0 then (1 / 2 : ENNReal) else w i)
                  hzmem).symm
      _ = (1 / 2 : ENNReal) +
          ∑ i ∈ (Finset.univ : Finset (Fin n)).erase z, w i := by
            rw [show z.val = 0 by rfl, if_pos rfl]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            have hiz : i ≠ z := (Finset.mem_erase.mp hi).1
            have hiv : i.val ≠ 0 := by
              intro hv
              exact hiz (Fin.ext hv)
            simp only [if_neg hiv]
      _ = (1 / 2 : ENNReal) +
          ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val), w i := by
            rw [hfilter]
  have hbasePos : ∀ᶠ base : Real in nhdsWithin (1 : Real) (Set.Iio 1),
      0 < base := by
    have hnear : ∀ᶠ base : Real in nhds (1 : Real), 0 < base := by
      exact isOpen_Ioi.mem_nhds (by norm_num : (1 : Real) ∈ Set.Ioi (0 : Real))
    exact nhdsWithin_le_nhds hnear
  have hbaseLt : ∀ᶠ base : Real in nhdsWithin (1 : Real) (Set.Iio 1),
      base < 1 := by
    filter_upwards [self_mem_nhdsWithin] with base hb
    exact hb
  have hcost := proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto n
  have hfull : Filter.Tendsto
      (fun base : Real =>
        ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ x : BitString n,
            runtimeSup (leadingOnesAdaptiveTransition
              (proposed_leadingOnes_referenceOptimalRate base))
              (leadingOnesTarget n) x))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (∑ i : Fin n, if i.val = 0 then (1 / 2 : ENNReal) else w i)) := by
    apply hcost.congr'
    filter_upwards [hbasePos, hbaseLt] with base hb0 hb1
    have hopt : ∀ j : Nat, j ≤ n →
        0 < proposed_leadingOnes_referenceOptimalRate base j ∧
        proposed_leadingOnes_referenceOptimalRate base j < 1 := by
      intro j _hj
      by_cases hj0 : j = 0
      · subst j
        simpa [proposed_leadingOnes_referenceOptimalRate] using
          (show 0 < base ∧ base < 1 from ⟨hb0, hb1⟩)
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        simpa only [proposed_leadingOnes_referenceOptimalRate, if_neg hj0,
          leadingOnesLocallyOptimalSchedule, one_div] using
          (proposed_leadingOnesAdaptive_optimalPositiveLevelRate_strict j hjpos)
    exact (proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum
      n (proposed_leadingOnes_referenceOptimalRate base) hopt).symm
  simpa only [hsplit] using hfull

end ECRuntime
