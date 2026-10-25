import ECRuntime.UnaryOneMaxHarmonicLowerWithoutSingleton
import Mathlib

open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07: bounds certified under a smaller upper cap on harmonic drift
remain valid when one only requests the weaker lower bound corresponding
to a larger positive cap. No general cap for arbitrary multi-bit
mutation is asserted. -/

/-- A harmonic drift cap can be safely relaxed before applying the
certified generic additive-drift runtime lower bound. -/
theorem proposed_unaryOneMax_harmonicRuntime_of_relaxedDriftCap
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (deltaSmall deltaLarge : Real)
    (hd0 : 0 < deltaSmall) (hdle : deltaSmall ≤ deltaLarge)
    (x : BitString n)
    (hcap : ∀ y : BitString n, y ≠ allOnes n →
      (Finset.sum Finset.univ (fun z : BitString n =>
        law.transition oneMaxReal y z *
        (harmonicReal (zeroCount y) - harmonicReal (zeroCount z)))) ≤ deltaSmall) :
    ENNReal.ofReal (harmonicReal (zeroCount x) / deltaLarge) ≤
      runtimeSup (law.transition oneMaxReal)
        ({allOnes n} : Set (BitString n)) x := by
  have hdlarge : 0 < deltaLarge := lt_of_lt_of_le hd0 hdle
  apply proposed_unaryOneMax_harmonicRuntime_of_driftCap
    hn law deltaLarge hdlarge x
  intro y hy
  exact (hcap y hy).trans hdle

end ECRuntime
