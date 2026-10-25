import ECRuntime.LogTwoHarmonicCorrectionFiniteSandwich
import Mathlib

open Filter
open scoped BigOperators

namespace ECRuntime

/-!
Stage 208, APPROVED theorem header (proof-20 attempt).

The previously certified finite enclosure of the logarithmic half-series
reduces the remaining random-initial-stake remainder to n / 2^n. We prove
the geometric decay with an elementary n^2 <= 2^n estimate, rather than
assuming any new power-series identity.
-/

/-- An elementary polynomial-versus-geometric comparison, sufficient for
showing that n / 2^n vanishes. The index 4 is sharp for this induction. -/
private theorem stage208_nat_square_le_two_pow
    (n : Nat) (hn : 4 <= n) : n * n <= 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) * (n + 1) <= 2 * (n * n) := by
          have hmul : 4 * n <= n * n := Nat.mul_le_mul_right n hn
          nlinarith [hmul]
        _ <= 2 * (2 ^ n) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- Scaled geometric decay; the eventual upper bound is 1/n. -/
private theorem stage208_nat_div_pow_two_tendsto_zero :
    Tendsto (fun n : Nat => (n : Real) / (2 : Real) ^ n)
      atTop (nhds (0 : Real)) := by
  have hupper : ∀ᶠ n : Nat in atTop,
      (n : Real) / (2 : Real) ^ n <= (1 : Real) / (n : Real) := by
    filter_upwards [Filter.eventually_ge_atTop (4 : Nat)] with n hn
    have hnat := stage208_nat_square_le_two_pow n hn
    have hreal : (n : Real) * (n : Real) <= (2 : Real) ^ n := by
      exact_mod_cast hnat
    have hp : (0 : Real) < (2 : Real) ^ n := by positivity
    have hnpos : (0 : Real) < (n : Real) := by
      exact_mod_cast (show 0 < n by omega)
    exact (div_le_div_iff₀ hp hnpos).2 (by simpa only [mul_one, one_mul] using hreal)
  apply squeeze_zero'
  · filter_upwards [] with n
    positivity
  · exact hupper
  · exact tendsto_one_div_atTop_nhds_zero_nat

/-- The scaled finite correction vanishes. No stronger assumption is used
than the already certified finite log-two series enclosure. -/
theorem proposed_randomInitialStake_scaledBinomialCorrection_tendsto_zero :
    Tendsto
      (fun n : Nat => (n : Real) *
        (Real.log 2 -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j))))
      atTop (nhds (0 : Real)) := by
  have hbound (n : Nat) :
      0 <= (n : Real) *
        (Real.log 2 - (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /\
      (n : Real) *
        (Real.log 2 - (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) <=
        (n : Real) / (2 : Real) ^ n := by
    have hfinite := proposed_logTwo_harmonicHalfSeries_finiteSandwich n
    have hnnonneg : (0 : Real) <= (n : Real) := Nat.cast_nonneg _
    constructor
    · exact mul_nonneg hnnonneg (sub_nonneg.mpr hfinite.1)
    · have hle : Real.log 2 -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)) <=
          (1 : Real) / (2 : Real) ^ n := by
        linarith [hfinite.2]
      calc
        _ <= (n : Real) * ((1 : Real) / (2 : Real) ^ n) :=
          mul_le_mul_of_nonneg_left hle hnnonneg
        _ = (n : Real) / (2 : Real) ^ n := by ring
  exact squeeze_zero (fun n => (hbound n).1) (fun n => (hbound n).2)
    stage208_nat_div_pow_two_tendsto_zero

end ECRuntime
