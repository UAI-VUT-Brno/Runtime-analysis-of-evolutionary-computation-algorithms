import ECRuntime.UnaryOneMaxMeanRadiusRuntimeLower
import ECRuntime.IndependentBitExpectedMutationRadius
import ECRuntime.OneMax
import Mathlib

open scoped ENNReal
namespace ECRuntime

/-! P07: use the distribution-free lower-drift theorem to obtain the
independent-bit (1+1)-EA zero-count lower bound with a concrete mutation rate. -/

/-- From a nonoptimal state, independent-bit mutation with 0 < p ≤ 1
requires at least d/(n*p) expected iterations to optimize OneMax. -/
theorem proposed_oneMaxEA_independentBit_runtimeSup_ge_zeroCount_div_np
    {n : Nat} (hn : 0 < n) (p : Real) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x : BitString n) (hx : x ≠ allOnes n) :
    ENNReal.ofReal ((zeroCount x : Real) / ((n : Real) * p)) ≤
      runtimeSup
        ((StaticUnaryUnbiasedMutation.independentBitLaw (n := n) p hp0.le hp1).transition
          oneMaxReal)
        ({allOnes n} : Set (BitString n)) x := by
  let law : StaticUnaryUnbiasedMutation n :=
    StaticUnaryUnbiasedMutation.independentBitLaw p hp0.le hp1
  have hmean : 0 < law.meanRadius := by
    dsimp [law]
    rw [proposed_independentBitLaw_meanRadius_eq_n_mul_p n p hp0.le hp1]
    exact mul_pos (by exact_mod_cast hn) hp0
  have hlower := proposed_unaryOneMax_runtimeSup_ge_zeroCount_div_meanRadius
    hn law hmean x hx
  have hident : law.meanRadius = (n : Real) * p :=
    proposed_independentBitLaw_meanRadius_eq_n_mul_p n p hp0.le hp1
  rw [hident] at hlower
  exact hlower

end ECRuntime
