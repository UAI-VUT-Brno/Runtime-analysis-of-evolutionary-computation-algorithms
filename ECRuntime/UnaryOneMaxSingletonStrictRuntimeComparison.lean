import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import ECRuntime.UnaryOneMaxSingletonStrictRateComparison
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: transfer the strict real-valued singleton-rate comparison into
the actual extended-real hitting time.  The start must be nonoptimal:
when zeroCount x = 0, both runtimes vanish and strict comparison is false. -/

/-- For a nonoptimal OneMax start, a singleton-only unary law with greater
positive one-bit mass has strictly smaller genuine expected runtime. -/
theorem proposed_unaryOneMax_singletonMass_strictExpectedRuntime
    {n : Nat} (hn : 0 < n)
    (slow fast : StaticUnaryUnbiasedMutation n)
    (hs : 0 < slow.oneBitMass)
    (hf : slow.oneBitMass < fast.oneBitMass)
    (hslow : forall mask : MutationMask n,
      slow.weight mask ≠ 0 -> mask.card ≤ 1)
    (hfast : forall mask : MutationMask n,
      fast.weight mask ≠ 0 -> mask.card ≤ 1)
    (x : BitString n) (hx : 0 < zeroCount x) :
    runtimeSup (fast.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x <
    runtimeSup (slow.transition oneMaxReal)
      ({allOnes n} : Set (BitString n)) x := by
  have hfp : 0 < fast.oneBitMass := lt_trans hs hf
  rw [proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
        hn fast hfp hfast x,
      proposed_unaryOneMax_singletonRuntime_eq_harmonic_withoutMeanHyp
        hn slow hs hslow x]
  have hlt := proposed_unaryOneMax_singletonRate_strictRuntimeFactor
    hn (zeroCount x) hx slow.oneBitMass fast.oneBitMass hs hf
  apply (ENNReal.ofReal_lt_ofReal_iff').2
  constructor
  · exact hlt
  · have hdim : (0 : Real) < n := Nat.cast_pos.mpr hn
    have hH : 0 < harmonicReal (zeroCount x) := by
      have hstep := harmonicReal_add_inv_le_of_lt (j := 0) (k := zeroCount x) hx
      have hinv : (0 : Real) < (zeroCount x : Real)⁻¹ :=
        inv_pos.mpr (Nat.cast_pos.mpr hx)
      have hle : (zeroCount x : Real)⁻¹ ≤ harmonicReal (zeroCount x) := by
        simpa using hstep
      exact lt_of_lt_of_le hinv hle
    exact mul_pos (div_pos hdim hs) hH

end ECRuntime
