import ECRuntime.UnaryOneMaxSingletonExactHarmonicRuntime
import ECRuntime.StaticUnarySingletonSupportMeanRadius
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: a statement of the exact harmonic runtime requiring only the
mathematically natural support and positivity assumptions. The redundant
mean-radius equality is discharged by Stage 414. -/

/-- The exact harmonic runtime for any positive singleton-supported unary law,
without separately assuming that its mean radius equals its one-bit mass. -/
theorem proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (hone : 0 < law.oneBitMass)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1)
    (x : BitString n) :
    runtimeSup (law.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x =
    ENNReal.ofReal
      (((n : Real) / law.oneBitMass) * harmonicReal (zeroCount x)) := by
  exact proposed_unaryOneMax_singletonRuntime_eq_scaledHarmonic
    hn law hone hsmall
    (proposed_staticUnary_singletonSupport_meanRadius_eq_oneBitMass law hsmall)
    x

end ECRuntime
