import Mathlib

namespace ECRuntime

/-! P01: real-valued boundary continuity for the level-zero term of the
full adaptive LeadingOnes runtime. This is a separate analytic ingredient
for the ENNReal limit statement in Stage 420. -/

/-- The real level-zero residence contribution approaches one half as the
rate approaches one from below. -/
theorem proposed_leadingOnes_referenceZero_realBoundaryLimit :
    Filter.Tendsto (fun base : Real => (1 / 2 : Real) / base)
      (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (1 / 2 : Real)) := by
  have hcont : ContinuousAt (fun base : Real => (1 / 2 : Real) / base) 1 :=
    continuousAt_const.div continuousAt_id (by norm_num)
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

end ECRuntime
