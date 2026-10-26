import ECRuntime.UnaryOneMaxMeanRadiusRuntimeLower
import ECRuntime.StaticUnaryMeanRadiusBound
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: dimensional lower bound for every positive-mean static unary
mutation distribution, including multi-bit operators. -/

/-- Initial zero count divided by n lower-bounds OneMax runtime under
any positive-mean static unary-unbiased mutation law. -/
theorem proposed_unaryOneMax_runtimeSup_ge_zeroCount_div_dimension
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n) (hmean : 0 < law.meanRadius)
    (x : BitString n) (hx : x ≠ allOnes n) :
    ENNReal.ofReal ((zeroCount x : Real) / (n : Real)) ≤
      runtimeSup (law.transition (oneMaxReal (n := n)))
        ({allOnes n} : Set (BitString n)) x := by
  have hposn : 0 < (n : Real) := by exact_mod_cast hn
  have hmeanLe : law.meanRadius ≤ (n : Real) :=
    proposed_staticUnary_meanRadius_le_dimension law
  have hzeroNonneg : (0 : Real) ≤ (zeroCount x : Real) :=
    Nat.cast_nonneg _
  have hratio :
      (zeroCount x : Real) / (n : Real) ≤
        (zeroCount x : Real) / law.meanRadius := by
    apply (div_le_div_iff₀ hposn hmean).2
    exact mul_le_mul_of_nonneg_left hmeanLe hzeroNonneg
  exact (ENNReal.ofReal_le_ofReal hratio).trans
    (proposed_unaryOneMax_runtimeSup_ge_zeroCount_div_meanRadius
      hn law hmean x hx)

end ECRuntime
