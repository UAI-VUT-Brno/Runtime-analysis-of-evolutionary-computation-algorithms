import ECRuntime.UnaryOneMaxHarmonicLowerWithoutSingleton
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: specialize the abstract harmonic progress cap to a natural
chi/n per-step scale. This explicitly retains the one-step drift condition:
without it, multi-bit jumps invalidate a universal harmonic runtime bound. -/

/-- A harmonic drift cap chi/n yields an n/chi harmonic runtime bound. -/
theorem proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (chi : Real) (hchi : 0 < chi)
    (x : BitString n)
    (hcap : forall y : BitString n, y != allOnes n ->
      (Finset.sum Finset.univ (fun z : BitString n =>
        (law.transition oneMaxReal) y z *
          (harmonicReal (zeroCount y) - harmonicReal (zeroCount z))))
            <= chi / (n : Real)) :
    ENNReal.ofReal (((n : Real) / chi) * harmonicReal (zeroCount x)) <=
      runtimeSup (law.transition oneMaxReal)
        ({allOnes n} : Set (BitString n)) x := by
  have hdim : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hdelta : 0 < chi / (n : Real) := div_pos hchi hdim
  have hcapProp : ∀ y : BitString n, y ≠ allOnes n →
      (Finset.sum Finset.univ (fun z : BitString n =>
        (law.transition oneMaxReal) y z *
          (harmonicReal (zeroCount y) - harmonicReal (zeroCount z))))
        ≤ chi / (n : Real) := by
    intro y hy
    exact hcap y (by simp [hy])
  have h := proposed_unaryOneMax_harmonicRuntime_of_driftCap
    hn law (chi / (n : Real)) hdelta x hcapProp
  convert h using 1
  congr 1
  field_simp

end ECRuntime
