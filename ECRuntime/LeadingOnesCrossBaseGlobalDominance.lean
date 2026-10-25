import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import ECRuntime.LeadingOnesBoundaryGlobalInfimum
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: jointly apply the certified fixed-base global minimizer and
monotonicity in the level-zero base rate. Neither hypothesis can be dropped
without changing the range of admissible adaptive schedules. -/

/-- The reference schedule at a larger level-zero rate beats any interior
schedule at the smaller prescribed level-zero rate. -/
theorem proposed_leadingOnes_referenceCrossBase_uniformRuntime_dominates
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (base1 base2 : Real)
    (hb1 : 0 < base1) (horder : base1 <= base2) (hb2 : base2 < 1)
    (rate : Nat -> Real)
    (hinterior : forall j : Nat, j <= n -> 0 < rate j /\ rate j < 1)
    (hzero : rate 0 = base1) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (Finset.sum Finset.univ (fun x : BitString n =>
        runtimeSup (leadingOnesAdaptiveTransition
          (proposed_leadingOnes_referenceOptimalRate base2))
          (leadingOnesTarget n) x)) <=
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (Finset.sum Finset.univ (fun x : BitString n =>
        runtimeSup (leadingOnesAdaptiveTransition rate)
          (leadingOnesTarget n) x)) := by
  exact (proposed_leadingOnes_referenceRate_monotoneBase_uniformRuntime
    n base1 base2 hb1 horder hb2).trans
    (proposed_leadingOnes_referenceOptimal_uniformRuntime_minimal
      n base1 hb1 (lt_of_le_of_lt horder hb2) rate hinterior hzero)

end ECRuntime
