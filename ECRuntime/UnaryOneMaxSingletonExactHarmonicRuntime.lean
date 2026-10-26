import ECRuntime.UnaryOneMaxSingletonHarmonicRuntimeLower
import ECRuntime.OneMaxUnaryHarmonic
import ECRuntime.UnrestrictedRuntime
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: sharpen the presently one-sided harmonic progress lemma to an
exact runtime law for unary-unbiased mutation supported on no-op and
singleton masks. This requires relating singleton mass to mean radius
and proving compatibility of the two target DecidablePred instances. -/

/-- The coupon-collector harmonic runtime is exact when every nontrivial
mutation flips exactly one uniformly chosen coordinate. -/
theorem proposed_unaryOneMax_singletonRuntime_eq_scaledHarmonic
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (hone : 0 < law.oneBitMass)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1)
    (hchi : law.meanRadius = law.oneBitMass)
    (x : BitString n) :
    runtimeSup (law.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x =
    ENNReal.ofReal
      (((n : Real) / law.oneBitMass) * harmonicReal (zeroCount x)) := by
  classical
  have hmean : 0 < law.meanRadius := by rw [hchi]; exact hone
  have htarget : oneMaxTarget n =
      ({allOnes n} : Set (BitString n)) :=
    oneMaxTarget_eq_singleton n
  have hupper := StaticUnaryUnbiasedMutation.oneMaxUnary_runtimeSup_le_harmonic
    law hn hone x
  have hbridge := runtimeSup_congr_target (law.transition oneMaxReal)
    (oneMaxTarget n) ({allOnes n} : Set (BitString n)) htarget x
  have hupper' :
      runtimeSup (law.transition oneMaxReal)
        ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal
        (((n : Real) / law.oneBitMass) * harmonicReal (zeroCount x)) := by
    rw [← hbridge]
    exact hupper
  by_cases hx : x = allOnes n
  · subst x
    have hzero :
        ENNReal.ofReal
          (((n : Real) / law.oneBitMass) *
            harmonicReal (zeroCount (allOnes n))) = 0 := by
      simp [zeroCount_allOnes, harmonicReal_zero]
    rw [hzero] at hupper' ⊢
    exact le_antisymm hupper' bot_le
  · have hlower := proposed_unaryOneMax_singletonRuntime_ge_harmonic_div_rate
      hn law hmean hsmall x hx
    have hposn : (n : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hp : law.oneBitMass ≠ 0 := ne_of_gt hone
    have hratio :
        harmonicReal (zeroCount x) / (law.meanRadius / (n : Real)) =
          ((n : Real) / law.oneBitMass) * harmonicReal (zeroCount x) := by
      rw [hchi]
      field_simp
    rw [hratio] at hlower
    exact le_antisymm hupper' hlower

end ECRuntime
