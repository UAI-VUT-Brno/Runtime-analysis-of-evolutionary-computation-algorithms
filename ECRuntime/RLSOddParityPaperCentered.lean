import ECRuntime.StrictMonotoneRLSOddSharpCentered
import Mathlib

open Filter
namespace ECRuntime

/-! Stage 247 (P02, approved statement; compiler-clean in proof-32).
The Doerr--Doerr paper defines H_{n/2} for odd n=2m+1 to be the
arithmetic average (H_m + H_{m+1})/2. Unlike H_m + 1/n, this
is an exact source-matched convention. Since the scaled change of
centering is (2m+1)/(2(m+1)) -> 1, the existing +1/2 odd limit
becomes -1/2. This still establishes an odd-subsequence claim, not
an all-dimension limit. -/

/-- Sharp odd-dimension RLS runtime centered using the published
half-harmonic convention, for every strictly monotone fitness family. -/
theorem proposed_strictMonotoneRLS_oddPaperHalfHarmonicCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun m : Nat =>
        strictMonotoneRLSUniformInitialMean
          (show 0 < 2 * m + 1 by omega) (fitness (2 * m + 1)) -
          (((2 * m + 1 : Nat) : Real) *
            ((harmonicReal m + harmonicReal (m + 1)) / 2)))
      atTop (nhds (-(1 / 2 : Real))) := by
  have hOdd := proposed_strictMonotoneRLS_uniformInitial_oddSharpCentered fitness hf
  have hshift : Tendsto (fun m : Nat => m + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => (show m ≤ m + 1 by omega)))
      tendsto_id
  have hcast : Tendsto (fun m : Nat => (((m + 1 : Nat) : Real)))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hshift
  have hinv : Tendsto (fun m : Nat => (((m + 1 : Nat) : Real)⁻¹))
      atTop (nhds (0 : Real)) := tendsto_inv_atTop_zero.comp hcast
  have hsmall : Tendsto (fun m : Nat =>
      (1 / 2 : Real) * (((m + 1 : Nat) : Real)⁻¹))
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hinv.const_mul (1 / 2 : Real)
  have hone : Tendsto (fun _ : Nat => (1 : Real))
      atTop (nhds (1 : Real)) := tendsto_const_nhds
  have hcorrection := hone.sub hsmall
  have hcenter := hOdd.sub hcorrection
  have hval : (1 / 2 : Real) - (1 - 0) = -(1 / 2 : Real) := by norm_num
  rw [hval] at hcenter
  apply hcenter.congr'
  filter_upwards [] with m
  have hsucc : harmonicReal (m + 1) =
      harmonicReal m + (((m + 1 : Nat) : Real)⁻¹) := by
    simp [harmonicReal, harmonic_succ]
  have hcast : ((2 * m + 1 : Nat) : Real) =
      2 * (((m + 1 : Nat) : Real)) - 1 := by
    push_cast
    ring
  have hmne : (((m + 1 : Nat) : Real)) ≠ 0 := by positivity
  rw [hsucc, hcast]
  field_simp [hmne]
  ring

end ECRuntime
