import ECRuntime.LeadingOnesMainResults
import ECRuntime.WittMutationLogThreeRuntime

open ECRuntime

/-!
# Non-vacuity witnesses

A theorem with unsatisfiable hypotheses is vacuously true and says nothing. Every
facade result below is therefore instantiated at a concrete point that discharges
*all* of its hypotheses simultaneously, including the instance arguments.

These examples deliberately avoid forcing the concrete statements to reduce:
instantiating, say, `leadingOnesUniformFirstHittingTimeExpectation 4` as an equation
makes the elaborator evaluate `Fintype.card (BitString 4)` and the whole sum, which
times out and tests nothing useful. Applying the theorem is what establishes that the
hypothesis set is inhabited.
-/

namespace ECRuntimeTest

/-- The Witt log-three interval is non-degenerate: it contains the standard scale `c = 1`.

This is the arithmetic content of `c ≤ log 3` being a genuine constraint rather than an
empty one, and it is what lets the witness below use `c = 1`. -/
theorem one_le_logThreeScale : (1 : ℝ) ≤ wittMutationC3LogThreeScale := by
  rw [wittMutationC3LogThreeScale_eq, Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  linarith

/-- The log-three scale is strictly positive, so `0 < c ≤ log 3` is a non-empty range. -/
theorem logThreeScale_pos : 0 < wittMutationC3LogThreeScale :=
  lt_of_lt_of_le zero_lt_one one_le_logThreeScale

/-- The LeadingOnes hypothesis set is satisfiable.

The measurability instances are inhabited (the discrete `⊤` structure works, and makes
every singleton measurable), and `p = 1/2` satisfies `0 < p < 1`. -/
example : True := by
  letI : MeasurableSpace (BitString 4) := ⊤
  haveI : MeasurableSingletonClass (BitString 4) := ⟨fun _ => trivial⟩
  have _witness := leadingOnesUniformFirstHittingTimeExpectation_eq_formula
    (n := 4) (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  trivial

/-- The Witt log-three runtime hypothesis set is satisfiable.

`n = 4` meets `4 ≤ n`; `c = 1` meets `0 < c ≤ log 3` by `one_le_logThreeScale`; and the
constant weight vector `w ≡ 1` is both positive and nonincreasing. -/
example : True := by
  have _witness := wittMutation_runtimeSup_le_logThreeScale_log_bound
    (n := 4) (by norm_num) (c := 1) (by norm_num) one_le_logThreeScale
    (fun _ => (1 : ℝ)) (fun _ => by norm_num) (fun _ _ _ => le_refl _) (allZeros 4)
  trivial

/-- The same witness discharges the exact-rate envelope on the log-three interval. -/
example : True := by
  have _witness := wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale
    (n := 4) (by norm_num) (c := 1) (by norm_num) one_le_logThreeScale
    (fun _ => (1 : ℝ)) (fun _ => by norm_num) (fun _ _ _ => le_refl _) (allZeros 4)
  trivial

end ECRuntimeTest
