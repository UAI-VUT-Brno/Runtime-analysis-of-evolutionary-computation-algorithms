import ECRuntime.RandomInitialStakeEvenHarmonicTail
import ECRuntime.FitnessLevel
import ECRuntime.RandomInitialStakeSharpEvenSandwich
import Mathlib

open Filter

namespace ECRuntime

/-!
# Stage 176 pending: sharp even-parity random-stake correction

Source direction: Doerr--Doerr, Collecting Coupons with Random Initial Stake.
Stage 172 certifies the even upper-half harmonic identity. The missing
analytic part of the published sharp mean is a second-order estimate for that
tail relative to log(2). This proposed limit isolates exactly the even-index
term giving the additive -1/2 correction after scaling by n = 2m.

Unlike the Stage 172 exact finite identity, this is a genuine asymptotic
result and its proof is NOT supplied. Odd dimensions require separate care;
no complete-paper claim follows from this candidate.

The theorem header was approved in the Round-5 follow-up. The exact
finite-difference reduction below is an intermediate algebraic fact; the
rate-sensitive asymptotic theorem remains open and out of public imports.
The finite alternating-pair identity reduces the problem to bounding a
reciprocal-quadratic tail. The asymptotic cannot follow from mere convergence
of harmonicReal n - log n: it needs an O(1/n) estimate with exact coefficient.
-/


/-- A dyadic harmonic-tail step has an exact positive rational increment.
This recurrence reduces the sharp `-1/2` limit to the tail of a reciprocal
quadratic sequence. It does not replace the required asymptotic estimate. -/
theorem stage176_evenHarmonicTail_step (m : Nat) :
    (harmonicReal (2 * (m + 1)) - harmonicReal (m + 1)) -
        (harmonicReal (2 * m) - harmonicReal m) =
      ((2 * m + 1 : Nat) : Real)⁻¹ -
        ((2 * m + 2 : Nat) : Real)⁻¹ := by
  have hsuccM : harmonicReal (m + 1) =
      harmonicReal m + ((m + 1 : Nat) : Real)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  have hsucc2M : harmonicReal (2 * m + 1) =
      harmonicReal (2 * m) + ((2 * m + 1 : Nat) : Real)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  have hsucc2M' : harmonicReal (2 * m + 2) =
      harmonicReal (2 * m + 1) + ((2 * m + 2 : Nat) : Real)⁻¹ := by
    -- The recurrence reduces to cast_add / cast_mul normalization.
    -- `simp` alone leaves `2 * ↑m + 1 + 1 = 2 * ↑m + 2`.
    have hidx : 2 * m + 2 = (2 * m + 1) + 1 := by omega
    rw [hidx]
    simp [harmonicReal, harmonic_succ]
  have htwo : ((2 * m + 2 : Nat) : Real) =
      2 * ((m + 1 : Nat) : Real) := by
    push_cast
    ring
  have hinv : ((m + 1 : Nat) : Real)⁻¹ =
      2 * (((2 * m + 2 : Nat) : Real)⁻¹) := by
    have hm : ((m + 1 : Nat) : Real) ≠ 0 := by positivity
    rw [htwo]
    field_simp
  have hidx : 2 * (m + 1) = (2 * m + 2 : Nat) := by omega
  rw [hidx, hsuccM, hsucc2M', hsucc2M, hinv]
  ring

/-- Exact finite dyadic expansion: the upper-half harmonic tail is the
first `m` alternating odd/even reciprocal pairs. Together with the
limit to `log 2`, this exposes the reciprocal-quadratic remainder whose
scaled limit supplies the sharp correction. -/
theorem stage176_evenHarmonicTail_alternatingPairs (m : Nat) :
    harmonicReal (2 * m) - harmonicReal m =
      (Finset.range m).sum (fun j =>
        ((2 * j + 1 : Nat) : Real)⁻¹ - ((2 * j + 2 : Nat) : Real)⁻¹) := by
  induction m with
  | zero => simp [harmonicReal]
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hstep := stage176_evenHarmonicTail_step m
      linarith

/-- The even upper-half harmonic tail differs from `log 2` by
`-1/(4m) + o(1/m)`. Multiplying by the dimension `2m` yields `-1/2`.
This is the analytic bridge needed for the even case of the sharper mean. -/
theorem proposed_randomInitialStake_evenSharpHalfHarmonicCorrection :
    Tendsto
      (fun m : Nat =>
        ((2 * m : Nat) : Real) *
          (harmonicReal (2 * m) - harmonicReal m - Real.log 2))
      atTop (nhds (-(1 / 2 : Real))) := by
  exact stage189_evenSharp_of_finiteSandwich
    (fun m hm => proposed_randomInitialStake_evenTail_sharpSandwich m hm)

end ECRuntime
