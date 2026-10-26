import ECRuntime.RLSAllDimensionPaperCenteredExact
import ECRuntime.RLSOddParityPaperCentered
import ECRuntime.StrictMonotoneRLSEvenSharpCentered
import Mathlib

open Filter

namespace ECRuntime

/-!
Stage 253 (P02): approved statement, pending complete proof verification. The exact all-dimension
formula (Stage 250), certified even-dimension sharp limit, and certified
odd-dimension *paper-centered* sharp limit agree at additive -1/2.
The only missing work is a full-sequence gluing theorem. Do not mistake
subsequence convergence for the stated atTop convergence.
-/

/-- Two convergent parity subsequences determine the limit of a sequence
on the natural numbers. This elementary gluing principle does not assume
monotonicity of the runtime sequence. -/
private theorem stage253_tendsto_of_even_odd
    {alpha : Type*} [TopologicalSpace alpha]
    (f : Nat → alpha) (x : alpha)
    (he : Tendsto (fun m : Nat => f (2 * m)) atTop (nhds x))
    (ho : Tendsto (fun m : Nat => f (2 * m + 1)) atTop (nhds x)) :
    Tendsto f atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro s hs
  rcases (Filter.eventually_atTop.1 (he.eventually_mem hs)) with ⟨Ne, hNe⟩
  rcases (Filter.eventually_atTop.1 (ho.eventually_mem hs)) with ⟨No, hNo⟩
  apply Filter.eventually_atTop.2
  refine ⟨2 * max Ne No + 2, ?_⟩
  intro n hn
  by_cases heven : n % 2 = 0
  · have hfactor : n = 2 * (n / 2) := by omega
    have hge : Ne ≤ n / 2 := by omega
    rw [hfactor]
    exact hNe _ hge
  · have hfactor : n = 2 * (n / 2) + 1 := by omega
    have hge : No ≤ n / 2 := by omega
    rw [hfactor]
    exact hNo _ hge

/-- Sharp all-dimensional additive RLS correction using the paper's
half-harmonic convention `H_(n/2) = (H_floor + H_ceil) / 2`.
The `n=0` branch is immaterial to the atTop limit. -/
theorem proposed_strictMonotoneRLS_allDimensionPaperSharpCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun n : Nat =>
        if hn : 0 < n then
          strictMonotoneRLSUniformInitialMean hn (fitness n) -
            (n : Real) *
              ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2)
        else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  let F : Nat → Real := fun n =>
    if hn : 0 < n then
      strictMonotoneRLSUniformInitialMean hn (fitness n) -
        (n : Real) *
          ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2)
    else 0
  have he : Tendsto (fun m : Nat => F (2 * m))
      atTop (nhds (-(1 / 2 : Real))) := by
    apply (proposed_strictMonotoneRLS_uniformInitial_evenSharpCentered fitness hf).congr'
    filter_upwards [] with m
    by_cases hm : m = 0
    · subst m
      simp [F]
    · have hpos : 0 < 2 * m := by omega
      have hd1 : (2 * m) / 2 = m := by omega
      have hd2 : (2 * m + 1) / 2 = m := by omega
      simp only [F, dif_pos hpos, hd1, hd2]
      ring
  have ho : Tendsto (fun m : Nat => F (2 * m + 1))
      atTop (nhds (-(1 / 2 : Real))) := by
    apply (proposed_strictMonotoneRLS_oddPaperHalfHarmonicCentered fitness hf).congr'
    filter_upwards [] with m
    have hpos : 0 < 2 * m + 1 := by omega
    have hd1 : (2 * m + 1) / 2 = m := by omega
    have hd2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    simp only [F, dif_pos hpos, hd1, hd2]
  exact stage253_tendsto_of_even_odd F (-(1 / 2 : Real)) he ho

end ECRuntime
