import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: on OneMax, singleton-supported static unary mutation laws with
the same one-bit mass have identical exact runtimes, even if their
zero-radius behavior is represented differently. -/

/-- Equal one-bit mass implies equal OneMax runtime for singleton laws. -/
theorem proposed_unaryOneMax_singletonLaw_runtimeInvariance
    {n : Nat} (hn : 0 < n)
    (law1 law2 : StaticUnaryUnbiasedMutation n)
    (hone : 0 < law1.oneBitMass)
    (hsmall1 : forall mask : MutationMask n,
      law1.weight mask ≠ 0 -> mask.card <= 1)
    (hsmall2 : forall mask : MutationMask n,
      law2.weight mask ≠ 0 -> mask.card <= 1)
    (heq : law1.oneBitMass = law2.oneBitMass)
    (x : BitString n) :
    runtimeSup (law1.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x =
    runtimeSup (law2.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x := by
  have htwo : 0 < law2.oneBitMass := by rwa [← heq]
  rw [proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
      hn law1 hone hsmall1 x,
      proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
      hn law2 htwo hsmall2 x,
      heq]

end ECRuntime
