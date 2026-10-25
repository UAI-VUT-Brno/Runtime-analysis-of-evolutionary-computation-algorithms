import ECRuntime.GenericFixedTargetAdditiveDriftLower
import ECRuntime.UnaryOneMaxExpectedProgressMeanRadius
import ECRuntime.OneMax
import ECRuntime.StaticUnaryUnbiasedMutation
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07. Unlike the independent-bit special case, this lower bound uses
no independence: any static unary-unbiased mask distribution with
positive mean radius is covered, including genuine multi-bit operators.
It follows from a proven uniform upper bound on accepted progress and
the residual-preserving lower additive drift theorem. -/

/-- For arbitrary static unary-unbiased elitist OneMax mutation, the
expected optimization time is at least the initial number of zero bits
divided by the mean mutation radius. -/
theorem proposed_unaryOneMax_runtimeSup_ge_zeroCount_div_meanRadius
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n) (hmean : 0 < law.meanRadius)
    (x : BitString n) (hx : x ≠ allOnes n) :
    ENNReal.ofReal ((zeroCount x : Real) / law.meanRadius) ≤
      runtimeSup (law.transition (oneMaxReal (n := n)))
        ({allOnes n} : Set (BitString n)) x := by
  classical
  have hP : IsStochastic (law.transition oneMaxReal) :=
    law.transition_stochastic _
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hstep : ∀ y : BitString n,
      y ∉ ({allOnes n} : Set (BitString n)) →
        (∑ z : BitString n,
          (law.transition oneMaxReal) y z *
            ((zeroCount y : Real) - (zeroCount z : Real))) ≤
          law.meanRadius := by
    intro y _hy
    have hfirst := proposed_unaryOneMax_expectedZeroDecrease_le_meanRadius
      hn law y
    have hz : (zeroCount y : Real) ≤ (n : Real) := by
      exact_mod_cast zeroCount_le y
    have hfrac : (zeroCount y : Real) / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnreal).2 (by simpa using hz)
    calc
      (∑ z : BitString n,
          (law.transition oneMaxReal) y z *
            ((zeroCount y : Real) - (zeroCount z : Real))) ≤
        (zeroCount y : Real) * (law.meanRadius / (n : Real)) := hfirst
      _ = ((zeroCount y : Real) / (n : Real)) * law.meanRadius := by ring
      _ ≤ 1 * law.meanRadius :=
        mul_le_mul_of_nonneg_right hfrac hmean.le
      _ = law.meanRadius := one_mul _
  -- The generic lower-drift theorem uses classical target membership, while
  -- the singleton target in this theorem has a computable DecidablePred.
  -- These are propositionally equal, not definitionally the same argument
  -- of the dependent `runtimeSup` expression.
  convert (proposed_genericFixedTarget_additiveDrift_runtimeLower
    (law.transition oneMaxReal) hP
    ({allOnes n} : Set (BitString n))
    (fun y => (zeroCount y : Real))
    (fun y => Nat.cast_nonneg (zeroCount y))
    (by intro y hy
        have hy' : y = allOnes n := Set.mem_singleton_iff.mp hy
        simp [hy'])
    law.meanRadius hmean hstep x (by simpa using hx)) using 1
  exact @runtimeSup_congr_target (BitString n) inferInstance
    (law.transition oneMaxReal)
    ({allOnes n} : Set (BitString n))
    ({allOnes n} : Set (BitString n))
    (fun a => Set.decidableSingleton a (allOnes n))
    (fun y => Classical.propDecidable (y ∈ ({allOnes n} : Set (BitString n))))
    rfl x

end ECRuntime
