import ECRuntime.WittStandardRuntime
import ECRuntime.AsymptoticRegime
import Mathlib

open scoped BigOperators ENNReal
open Filter
open Asymptotics
open MeasureTheory

namespace ECRuntime

/-!
# Stage 39: asymptotic presentation of the sharp standard-rate runtime bound

Stage 38 gives the compiler-verified finite-dimensional estimate

`runtime <= e n (2 + log n)`

for every positive nonincreasing linear objective at the standard mutation rate,
for `n >= 4`.  This module isolates the asymptotic presentation of that already
verified bound.  No new stochastic argument is introduced.

The finite upper envelope is split exactly into the leading term `e n log n`
and the linear correction `2 e n`.  The correction is then shown to be
`O(n)` under the repository-wide `atTop` convention from `AsymptoticRegime`.
Thus the Stage-38 endpoint is formally presented as

`e n log n + O(n)`.

The exponential-tail theorem remains a separate later stage because it requires
new generic multiplicative-drift probability infrastructure rather than mere
algebraic packaging of the verified expectation bound.
-/

/-- Leading `e n log n` term in the sharp standard-rate linear-runtime bound. -/
noncomputable def wittStandardRuntimeLeadingTerm (n : ℕ) : ℝ :=
  Real.exp 1 * natLinearLogGrowth n

/-- Linear correction appearing in the Stage-38 finite-dimensional bound. -/
noncomputable def wittStandardRuntimeLinearCorrection (n : ℕ) : ℝ :=
  (2 * Real.exp 1) * natLinearGrowth n

/-- The explicit finite-dimensional Stage-38 upper envelope. -/
noncomputable def wittStandardRuntimeUpperBound (n : ℕ) : ℝ :=
  (Real.exp 1 * (n : ℝ)) * (2 + Real.log (n : ℝ))

/-- The finite-dimensional upper envelope splits exactly into its leading term and
linear correction. -/
theorem wittStandardRuntimeUpperBound_eq_leading_add_linear
    (n : ℕ) :
    wittStandardRuntimeUpperBound n =
      wittStandardRuntimeLeadingTerm n +
        wittStandardRuntimeLinearCorrection n := by
  unfold wittStandardRuntimeUpperBound
    wittStandardRuntimeLeadingTerm
    wittStandardRuntimeLinearCorrection
    natLinearLogGrowth natLinearGrowth
  ring

/-- The correction term is `O(n)`. -/
theorem wittStandardRuntimeLinearCorrection_isBigO :
    NatIsBigO wittStandardRuntimeLinearCorrection natLinearGrowth := by
  unfold wittStandardRuntimeLinearCorrection
  exact Asymptotics.isBigO_const_mul_self
    (2 * Real.exp 1) natLinearGrowth Filter.atTop

/-- Formal `e n log n + O(n)` decomposition of the Stage-38 upper envelope. -/
theorem wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n :
    ∃ r : ℕ → ℝ,
      NatIsBigO r natLinearGrowth ∧
      ∀ n : ℕ,
        wittStandardRuntimeUpperBound n =
          wittStandardRuntimeLeadingTerm n + r n := by
  refine ⟨wittStandardRuntimeLinearCorrection,
    wittStandardRuntimeLinearCorrection_isBigO, ?_⟩
  intro n
  exact wittStandardRuntimeUpperBound_eq_leading_add_linear n

/-- Stage-38 runtime bound restated through the asymptotic upper-envelope name. -/
theorem wittStandard_runtimeSup_le_asymptotic_upperBound
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal (wittStandardRuntimeUpperBound n) := by
  unfold wittStandardRuntimeUpperBound
  exact wittStandard_runtimeSup_le_log_bound hn w hw hmono x

/-- The conventional sample-path expectation satisfies the same asymptotic envelope. -/
theorem wittStandard_firstHittingTime_lintegral_le_asymptotic_upperBound
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (oneMaxTarget n) x path
      ∂linearStandardTrajectoryMeasure (by omega) w x) ≤
      ENNReal.ofReal (wittStandardRuntimeUpperBound n) := by
  unfold wittStandardRuntimeUpperBound
  exact wittStandard_firstHittingTime_lintegral_le_log_bound hn w hw hmono x

/-- Equivalent explicit form: the sharp finite-dimensional runtime is bounded by
`e n log n + 2 e n`. -/
theorem wittStandard_runtimeSup_le_leading_add_linear
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (oneMaxTarget n) x ≤
      ENNReal.ofReal
        (wittStandardRuntimeLeadingTerm n +
          wittStandardRuntimeLinearCorrection n) := by
  rw [← wittStandardRuntimeUpperBound_eq_leading_add_linear n]
  exact wittStandard_runtimeSup_le_asymptotic_upperBound hn w hw hmono x

end ECRuntime
