import ECRuntime.UnaryOneMaxThresholdRuntimeLower
import ECRuntime.IndependentBitExpectedMutationRadius
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.OneMax
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: specialize the multibit-compatible threshold runtime lower
bound to the genuine independent-bit EA, with explicit n*p denominator. -/

/-- For p>0, reaching at most k zeros from d>k zeros takes at least
(d-k)/(n*p) iterations in extended expected runtime. -/
theorem proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np
    {n : Nat} (hn : 0 < n) (k : Nat) (p : Real)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x : BitString n) (hx : k < zeroCount x) :
    ENNReal.ofReal (((zeroCount x - k : Nat) : Real) / ((n : Real) * p)) ≤
      runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
        ({y : BitString n | zeroCount y ≤ k} : Set (BitString n)) x := by
  let law : StaticUnaryUnbiasedMutation n :=
    StaticUnaryUnbiasedMutation.independentBitLaw p hp0.le hp1
  have hmean : law.meanRadius = (n : Real) * p := by
    dsimp [law]
    exact proposed_independentBitLaw_meanRadius_eq_n_mul_p n p hp0.le hp1
  have hpos : 0 < law.meanRadius := by
    rw [hmean]
    exact mul_pos (by exact_mod_cast hn) hp0
  have hbound :=
    proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius
      hn k law hpos x hx
  rw [hmean] at hbound
  simpa only [law, StaticUnaryUnbiasedMutation.independentBitLaw_transition_eq_onePlusOneTransition]
    using hbound

end ECRuntime
