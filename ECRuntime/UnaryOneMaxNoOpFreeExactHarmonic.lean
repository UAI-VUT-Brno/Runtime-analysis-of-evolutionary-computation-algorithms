import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: the exact standard-RLS harmonic law is obtained for every
unary-unbiased mask law with full probability mass on singleton flips,
without requiring the law to be presented as a specific implementation. -/

/-- Singleton-only mutation has the exact n times harmonic OneMax runtime. -/
theorem proposed_unaryOneMax_noOpFree_singletonRuntime_eq_nHarmonic
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (hone : law.oneBitMass = 1)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1)
    (x : BitString n) :
    runtimeSup (law.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x =
    ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) := by
  have hpos : 0 < law.oneBitMass := by rw [hone]; norm_num
  rw [proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
    hn law hpos hsmall x]
  simp [hone]

end ECRuntime
