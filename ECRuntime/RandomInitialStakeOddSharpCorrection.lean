import ECRuntime.RandomInitialStakeOddScaledTailBridge
import ECRuntime.RandomInitialStakeEvenSharpCorrection
import Mathlib

open Filter

namespace ECRuntime

/-!
# Stage 186 proposal: odd-parity sharp random-initial-stake correction

Source: Doerr--Doerr, Collecting Coupons with Random Initial Stake.
Stage 182 certifies a finite parity bridge. If the currently open Stage 176
even-scaled correction tends to -1/2, the (2m+1)-scaled odd correction
must tend to +1/2. This is a *different sign* caused by the extra reciprocal
term in the odd harmonic tail. The analytic hypothesis is not yet certified.
The statement is approved; promotion still requires an admission-free proof
and the complete official gate checks.
-/


/-- Exact decomposition of the scaled odd discrepancy into the even scaled
    discrepancy, the unscaled even discrepancy, and one. This bridge is a
    finite algebraic identity; it is not itself the missing limit theorem. -/
theorem stage186_oddScaledTail_evenScaledDecomposition (m : Nat) :
    (((2 * m + 1 : Nat) : Real) *
       (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) =
    (((2 * m : Nat) : Real) *
       (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) +
       (harmonicReal (2 * m) - harmonicReal m - Real.log 2) + 1 := by
  rw [proposed_randomInitialStake_oddScaledTail_evenBridge]
  push_cast
  ring

/-- Proposed sharp odd-parity counterpart to the open Stage 176 limit. -/
theorem proposed_randomInitialStake_oddSharpHalfHarmonicCorrection :
    Tendsto
      (fun m : Nat =>
        (((2 * m + 1 : Nat) : Real) *
          (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)))
      atTop (nhds (1 / 2 : Real)) := by
  let D : Nat → Real := fun m =>
    harmonicReal (2 * m) - harmonicReal m - Real.log 2
  have hEven : Tendsto
      (fun m : Nat => ((2 * m : Nat) : Real) * D m)
      atTop (nhds (-(1 / 2 : Real))) := by
    simpa only [D] using
      proposed_randomInitialStake_evenSharpHalfHarmonicCorrection
  have hden : Tendsto (fun m : Nat => ((2 * m : Nat) : Real))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun m : Nat => by
        exact_mod_cast (by omega : m ≤ 2 * m)))
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : Nat => ((2 * m : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp hden
  have hprod : Tendsto
      (fun m : Nat =>
        (((2 * m : Nat) : Real) * D m) * ((2 * m : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hEven.mul hinv
  have hD : Tendsto D atTop (nhds (0 : Real)) := by
    apply hprod.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with m hm
    have hmne : ((2 * m : Nat) : Real) ≠ 0 := by
      have h : (2 * m : Nat) ≠ 0 := by omega
      exact_mod_cast h
    calc
      (((2 * m : Nat) : Real) * D m) * ((2 * m : Nat) : Real)⁻¹ =
          D m * (((2 * m : Nat) : Real) * ((2 * m : Nat) : Real)⁻¹) := by ring
      _ = D m := by rw [mul_inv_cancel₀ hmne, mul_one]
  have hsum : Tendsto
      (fun m : Nat =>
        (((2 * m : Nat) : Real) * D m) + D m + 1)
      atTop (nhds (1 / 2 : Real)) := by
    convert (hEven.add hD).add tendsto_const_nhds using 1; norm_num
  apply hsum.congr'
  filter_upwards [] with m
  simpa only [D] using
    (stage186_oddScaledTail_evenScaledDecomposition m).symm

end ECRuntime
