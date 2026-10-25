import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: zero-radius moves cannot improve the exact OneMax expected
runtime of a singleton-supported static unary operator. -/

/-- Positive singleton mass at most one gives runtime at least n H_d. -/
theorem proposed_unaryOneMax_singletonRuntime_ge_standardRLS
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (hone : 0 < law.oneBitMass)
    (honeLe : law.oneBitMass <= 1)
    (hsmall : forall mask : MutationMask n,
      law.weight mask ≠ 0 -> mask.card <= 1)
    (x : BitString n) :
    ENNReal.ofReal ((n : Real) * harmonicReal (zeroCount x)) <=
      runtimeSup (law.transition oneMaxReal)
        ({allOnes n} : Set (BitString n)) x := by
  rw [proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
    hn law hone hsmall x]
  apply ENNReal.ofReal_le_ofReal
  have hdim : 0 <= (n : Real) := Nat.cast_nonneg _
  have hscaled : (n : Real) <= (n : Real) / law.oneBitMass := by
    apply (le_div_iff₀ hone).2
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left honeLe hdim)
  exact mul_le_mul_of_nonneg_right hscaled
    (harmonicReal_nonneg (zeroCount x))

end ECRuntime
