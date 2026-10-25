import ECRuntime.RLSAllDimensionPaperSharpCentered
import Mathlib

open Filter

namespace ECRuntime

/-! Stage 259 (P02, approved statement; pending promotion). Explicit epsilon--N formulation
of the paper's parity-corrected all-dimensional sharp constant. It is
conditional on full Stage 253 certification and is deferred otherwise. -/

/-- Uniform-start one-bit RLS differs from the precise paper-centered
half-harmonic leading term by -1/2 with eventual error below any ε > 0. -/
theorem proposed_strictMonotoneRLS_allDimensionPaperSharpEpsilon
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n))
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ (n : Nat) (hn : 0 < n), N ≤ n →
      -(1 / 2 : Real) - eps <
        strictMonotoneRLSUniformInitialMean hn (fitness n) -
          (n : Real) *
            ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) ∧
        strictMonotoneRLSUniformInitialMean hn (fitness n) -
          (n : Real) *
            ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) <
          -(1 / 2 : Real) + eps := by
  have hlim := proposed_strictMonotoneRLS_allDimensionPaperSharpCentered fitness hf
  have hnhds : Set.Ioo (-(1 / 2 : Real) - eps) (-(1 / 2 : Real) + eps) ∈
      nhds (-(1 / 2 : Real)) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  rcases Filter.eventually_atTop.1 (hlim.eventually_mem hnhds) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hge
  simpa only [Set.mem_Ioo, dif_pos hn] using hN n hge

end ECRuntime
