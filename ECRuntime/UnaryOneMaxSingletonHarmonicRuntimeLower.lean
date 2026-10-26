import ECRuntime.GenericFixedTargetAdditiveDriftLower
import ECRuntime.UnaryOneMaxHarmonicProgressLowerResearch
import ECRuntime.OneMax
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: harmonic lower drift yields the logarithmic coupon-collector
scale for static unary operators supported on no-op/singleton masks.
The bounded-radius hypothesis is essential. -/

/-- Starting with d zero bits, the expected optimization time is at least
`H_d / (chi/n)` under a positive-mean singleton-supported mutation law. -/
theorem proposed_unaryOneMax_singletonRuntime_ge_harmonic_div_rate
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n) (hmean : 0 < law.meanRadius)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1)
    (x : BitString n) (hx : x ≠ allOnes n) :
    ENNReal.ofReal
      (harmonicReal (zeroCount x) / (law.meanRadius / (n : Real))) ≤
      runtimeSup (law.transition oneMaxReal)
        ({allOnes n} : Set (BitString n)) x := by
  classical
  have hP : IsStochastic (law.transition oneMaxReal) :=
    law.transition_stochastic _
  have hd : 0 < law.meanRadius / (n : Real) :=
    div_pos hmean (by exact_mod_cast hn)
  have hstep : ∀ y : BitString n,
      y ∉ ({allOnes n} : Set (BitString n)) →
        (∑ z : BitString n,
          (law.transition oneMaxReal) y z *
            (harmonicReal (zeroCount y) - harmonicReal (zeroCount z))) ≤
          law.meanRadius / (n : Real) := by
    intro y hy
    exact proposed_unaryOneMax_singletonHarmonicProgress_le_radiusDivN
      hn law hsmall y (by simpa using hy)
  -- The generic lower-drift theorem uses classical target membership, while
  -- the singleton target in this theorem has a computable DecidablePred.
  -- These are propositionally equal, not definitionally the same argument
  -- of the dependent `runtimeSup` expression.
  convert (proposed_genericFixedTarget_additiveDrift_runtimeLower
    (law.transition oneMaxReal) hP
    ({allOnes n} : Set (BitString n))
    (fun y => harmonicReal (zeroCount y))
    (fun y => harmonicReal_nonneg (zeroCount y))
    (by intro y hy
        have hy' : y = allOnes n := Set.mem_singleton_iff.mp hy
        simp [hy'])
    (law.meanRadius / (n : Real)) hd hstep x (by simpa using hx)) using 1
  exact @runtimeSup_congr_target (BitString n) inferInstance
    (law.transition oneMaxReal)
    ({allOnes n} : Set (BitString n))
    ({allOnes n} : Set (BitString n))
    (fun a => Set.decidableSingleton a (allOnes n))
    (fun y => Classical.propDecidable (y ∈ ({allOnes n} : Set (BitString n))))
    rfl x

end ECRuntime
