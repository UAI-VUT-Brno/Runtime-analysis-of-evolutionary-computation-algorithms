import ECRuntime.LeadingOnesReferenceZeroBoundaryRealLimit
import Mathlib

namespace ECRuntime

/-! P01: adding the base-independent finite positive-level real cost
preserves the limit of the level-zero reciprocal cost.  The further
conversion of the true runtime into this real expression remains a
separate, unproved ENNReal step. -/

/-- The real level-zero boundary limit is unchanged by a constant cost. -/
theorem proposed_leadingOnes_referenceZero_realBoundaryLimit_add
    (positiveLevelCost : Real) :
    Filter.Tendsto
      (fun base : Real => (1 / 2 : Real) / base + positiveLevelCost)
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds ((1 / 2 : Real) + positiveLevelCost)) := by
  exact proposed_leadingOnes_referenceZero_realBoundaryLimit.add
    tendsto_const_nhds

end ECRuntime
