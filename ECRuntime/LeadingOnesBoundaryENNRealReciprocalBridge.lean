import ECRuntime.LeadingOnesReferenceZeroBoundaryRealLimit
import ECRuntime.AdaptiveLeadingOnesUniformFullRuntime
import Mathlib

open scoped ENNReal
namespace ECRuntime

/-! P01: the analytic bridge from the certified *real* boundary limit to
its genuine extended-nonnegative-real residence contribution.  This is
an unconditional continuity statement.  Stage 420 additionally needs the
uniform-runtime-to-finite-sum identity and the remaining levelwise limits. -/

/-- The ENNReal residence contribution tends to one-half from below
when the level-zero mutation probability approaches one. -/
theorem proposed_leadingOnes_referenceZero_ennrealBoundaryLimit :
    Filter.Tendsto
      (fun base : Real => (1 / 2 : ENNReal) *
        ENNReal.ofReal (base⁻¹))
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (1 / 2 : ENNReal)) := by
  -- ENNReal multiplication is not globally continuous at 0 * infinity.
  -- Rewrite the product through ofReal and use continuity in Real instead.
  have hinv : Filter.Tendsto (fun base : Real => (1 : Real) / base)
      (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (1 : Real)) := by
    have hc : ContinuousAt (fun base : Real => (1 : Real) / base) 1 :=
      continuousAt_const.div continuousAt_id (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hreal : Filter.Tendsto
      (fun base : Real => (1 / 2 : Real) * (1 / base))
      (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (1 / 2 : Real)) := by
    simpa only [mul_one] using
      (tendsto_const_nhds.mul hinv : Filter.Tendsto
        (fun base : Real => (1 / 2 : Real) * (1 / base))
        (nhdsWithin (1 : Real) (Set.Iio 1))
        (nhds ((1 / 2 : Real) * (1 : Real))))
  have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : Real) := by
    simpa only [one_div] using ENNReal_ofReal_half.symm
  have hpoint (base : Real) :
      (1 / 2 : ENNReal) * ENNReal.ofReal (base⁻¹) =
        ENNReal.ofReal ((1 / 2 : Real) * (1 / base)) := by
    rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 1 / 2)]
    simp only [one_div]
  have hfun :
      (fun base : Real => (1 / 2 : ENNReal) * ENNReal.ofReal (base⁻¹)) =
        (fun base : Real => ENNReal.ofReal ((1 / 2 : Real) * (1 / base))) := by
    funext base
    exact hpoint base
  rw [hfun, hhalf]
  exact ENNReal.tendsto_ofReal hreal

end ECRuntime
