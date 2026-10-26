import ECRuntime.GenericFixedTargetAdditiveDriftLower
import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import ECRuntime.StaticUnaryUnbiasedMutation
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: seek a nontrivial general-operator harmonic-scale bound under
an explicit upper control of multi-bit accepted jumps. This is NOT
claimed for arbitrary unary mutation distributions: a radius-n
complement move provides a counterexample to a naive universal bound. -/

/-- A harmonic OneMax lower bound under an explicit harmonic drift cap. -/
theorem proposed_unaryOneMax_harmonicRuntime_of_driftCap
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (delta : Real) (hdelta : 0 < delta)
    (x : BitString n)
    (hcap : ∀ y : BitString n, y ≠ allOnes n →
      (∑ z : BitString n, (law.transition oneMaxReal) y z *
        (harmonicReal (zeroCount y) - harmonicReal (zeroCount z))) ≤ delta) :
    ENNReal.ofReal (harmonicReal (zeroCount x) / delta) ≤
      runtimeSup (law.transition oneMaxReal)
        ({allOnes n} : Set (BitString n)) x := by
  classical
  -- Retain the approved positivity assumption explicitly in the proof.
  have _positiveDimension : 0 < n := hn
  have hP : IsStochastic (law.transition oneMaxReal) :=
    law.transition_stochastic _
  have hpot : forall y : BitString n,
      0 <= harmonicReal (zeroCount y) := by
    intro y
    exact harmonicReal_nonneg _
  have hzero : forall y : BitString n,
      y ∈ ({allOnes n} : Set (BitString n)) ->
      harmonicReal (zeroCount y) = 0 := by
    intro y hy
    have heq : y = allOnes n := Set.mem_singleton_iff.mp hy
    simp [heq]
  have hstep : forall y : BitString n,
      y ∉ ({allOnes n} : Set (BitString n)) ->
      (Finset.sum Finset.univ (fun z : BitString n =>
        (law.transition oneMaxReal) y z *
          (harmonicReal (zeroCount y) - harmonicReal (zeroCount z))))
           <= delta := by
    intro y hy
    exact hcap y (by simpa using hy)
  by_cases hx : x = allOnes n
  · subst x
    simp [harmonicReal_zero]
  · convert (proposed_genericFixedTarget_additiveDrift_runtimeLower
      (law.transition oneMaxReal) hP
      ({allOnes n} : Set (BitString n))
      (fun y => harmonicReal (zeroCount y)) hpot hzero
      delta hdelta hstep x (by simpa using hx)) using 1
    exact @runtimeSup_congr_target (BitString n) inferInstance
      (law.transition oneMaxReal)
      ({allOnes n} : Set (BitString n))
      ({allOnes n} : Set (BitString n))
      (fun a => Set.decidableSingleton a (allOnes n))
      (fun y => Classical.propDecidable
        (y ∈ ({allOnes n} : Set (BitString n))))
      rfl x

end ECRuntime
