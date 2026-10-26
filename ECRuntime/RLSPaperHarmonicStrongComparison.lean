import ECRuntime.RLSAllDimensionSharpEpsilonBound
import ECRuntime.RLSAllDimensionPaperCenteredExact
import Mathlib

open Filter
namespace ECRuntime

/-! P02: exact paper representation is a uniform initial expectation;
its asymptotic is independent of every strictly coordinate-monotone
objective family. This is the precise source Theorem 2, stated in the
paper's +o(1) epsilon--N convention without any initial-evaluation shift. -/

/-- A literal epsilon--N positive-error representation of the sharp RLS
expected mutation-iteration asymptotic. -/
theorem proposed_strictMonotoneRLS_paperTheorem2_error_form
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun n : Nat => if hn : 0 < n then
        (strictMonotoneRLSUniformInitialMean hn (fitness n) + (1 / 2 : Real)) -
        (n : Real) * ((harmonicReal (n / 2) +
          harmonicReal ((n + 1) / 2)) / 2) else 0)
      atTop (nhds (0 : Real)) := by
  have h := proposed_strictMonotoneRLS_allDimensionPaperSharpCentered fitness hf
  have hshift := h.add_const (1 / 2 : Real)
  have hzero : (-(1 / 2 : Real)) + 1 / 2 = 0 := by norm_num
  rw [hzero] at hshift
  apply hshift.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with n hn
  have hnpos : 0 < n := by omega
  simp only [dif_pos hnpos]
  ring

end ECRuntime
