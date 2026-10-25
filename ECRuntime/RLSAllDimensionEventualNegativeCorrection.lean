import ECRuntime.RLSAllDimensionPaperSharpCentered
import Mathlib

open Filter
namespace ECRuntime

/-!
Stage 256 (P02, new proposal): a quantitative eventual finite-n consequence
of the sharp all-dimension asymptotic. This candidate is blocked until
Stage 253 is proved and promoted. It is not used as evidence for Stage 253.
-/

/-- For all sufficiently large dimensions the mean RLS runtime lies strictly
below the paper's exact half-harmonic center by at least 1/4 iteration. -/
theorem proposed_strictMonotoneRLS_eventually_belowPaperCenter
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    ∃ N : Nat, ∀ (n : Nat) (hpos : 0 < n), N ≤ n →
      strictMonotoneRLSUniformInitialMean hpos (fitness n) -
        (n : Real) *
          ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) <
        -(1 / 4 : Real) := by
  have h := proposed_strictMonotoneRLS_allDimensionPaperSharpCentered fitness hf
  have hevent : ∀ᶠ n : Nat in atTop,
      (if hn : 0 < n then
        strictMonotoneRLSUniformInitialMean hn (fitness n) -
          (n : Real) *
            ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2)
       else 0) < -(1 / 4 : Real) := by
    exact h.eventually (Iio_mem_nhds (by norm_num : -(1 / 2 : Real) < -(1 / 4 : Real)))
  rcases eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnpos hn
  simpa only [dif_pos hnpos] using hN n hn

end ECRuntime
