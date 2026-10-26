import ECRuntime.LeadingOnesResidenceMean
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-- Membership in the canonical LeadingOnes optimum target is decidable.  The
assembly layer uses `runtimeSup` and the trajectory first-hitting-time API, both of
which require a `DecidablePred` instance for the target set. -/
noncomputable instance instDecidablePredLeadingOnesTarget (n : ℕ) :
    DecidablePred (fun x : BitString n => x ∈ leadingOnesTarget n) := by
  classical
  intro x
  change Decidable (x = allOnes n)
  infer_instance

/-!
# Stage 27 fix 12: algebraic assembly of the exact LeadingOnes runtime formula

Stage 27 fix 11 compiler-verifies the exact conditional mean residence at every visited
LeadingOnes level,

  `1 / (p * (1-p)^i)`,

while Stage 27 fix 9 fix 2 compiler-verifies that every nonterminal exact level is
visited with uniform-initialization mass `1/2` when `0 < p < 1`.

This file assembles those promoted ingredients without silently identifying them with
an infinite-path expectation.  It introduces two canonical quantities:

* the genuine uniform-initialization sample-path first-hitting-time expectation, defined
  as the finite uniform average of the existing trajectory `lintegral` expectations;
* the countable first-entry-mass times conditional-mean-residence series.

The latter is proved exactly equal to the closed finite level sum

  `(1/2) * sum_i (p * (1-p)^i)^(-1)`.

Thus, after this slice, the only missing theorem for the exact expected runtime is a
single representation bridge identifying the actual pathwise runtime expectation with
the assembled level-residence contribution.  That bridge can be attacked separately
using the existing first-entry finite-history semantics and level-charge decomposition.
-/

/-- Infinite trajectory law of the LeadingOnes `(1+1)` EA from a fixed initial state. -/
noncomputable def leadingOnesTrajectoryMeasure
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n) :
    Measure (ℕ → BitString n) :=
  transitionTrajectoryMeasure
    (onePlusOneTransition p (leadingOnesReal (n := n)))
    (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
    x

/-- Genuine uniform-initialization expected optimization time, kept in `ENNReal`.
The initial search point is averaged uniformly over all bit strings; conditional on
that point, the expectation is the `lintegral` of the conventional first-hitting time
under the verified infinite trajectory law. -/
noncomputable def leadingOnesUniformFirstHittingTimeExpectation
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ENNReal :=
  ((Fintype.card (BitString n) : ENNReal)⁻¹) *
    ∑ x : BitString n,
      ∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x

/-- The genuine sample-path definition is equivalently the uniform average of the
existing Bellman `runtimeSup` quantity.  This theorem fixes the exact target that the
level-residence representation bridge must identify. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_runtimeSup_average
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0 hp1 =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          runtimeSup
            (onePlusOneTransition p (leadingOnesReal (n := n)))
            (leadingOnesTarget n) x := by
  classical
  unfold leadingOnesUniformFirstHittingTimeExpectation
  apply congrArg
    (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro x _hx
  unfold leadingOnesTrajectoryMeasure
  exact transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
    (onePlusOneTransition p (leadingOnesReal (n := n)))
    (leadingOnesTarget n)
    (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
    x

/-- The promoted conditional mean residence is nonnegative in the nondegenerate
mutation regime. -/
theorem leadingOnesVisitedLevelMeanResidence_nonneg
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    0 ≤ leadingOnesVisitedLevelMeanResidence p i := by
  unfold leadingOnesVisitedLevelMeanResidence
  exact inv_nonneg.mpr
    (leadingOnesLevelExitProbability_pos hp0 hp1 i).le

/-- Countable contribution of exact first entries into level `i`, with each entry mass
multiplied by the exact conditional mean residence verified in Stage 27 fix 11. -/
noncomputable def leadingOnesUniformLevelResidenceContribution
    {n : ℕ} (p : ℝ) (i : Fin n) : ENNReal :=
  ∑' t : ℕ,
    ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i) *
      ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i)

/-- The entry-residence series factors into eventual exact-entry mass times the exact
conditional mean residence. -/
theorem leadingOnesUniformLevelResidenceContribution_eq_visitMass_mul_mean
    {n : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesUniformLevelResidenceContribution p i =
      leadingOnesUniformLevelVisitMass p i *
        ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) := by
  unfold leadingOnesUniformLevelResidenceContribution
  calc
    (∑' t : ℕ,
        ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i) *
          ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i)) =
        ∑' t : ℕ,
          ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) *
            ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i) := by
      apply tsum_congr
      intro t
      rw [mul_comm]
    _ = ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) *
        (∑' t : ℕ,
          ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i)) := by
      exact ENNReal.tsum_mul_left
    _ = (∑' t : ℕ,
          ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i)) *
        ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) := by
      rw [mul_comm]
    _ = leadingOnesUniformLevelVisitMass p i *
        ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) := by
      rfl

/-- Under `0 < p < 1`, the exact expected residence contribution of one level is one
half of its conditional mean residence. -/
theorem leadingOnesUniformLevelResidenceContribution_eq_ofReal_half_mean
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesUniformLevelResidenceContribution p i =
      ENNReal.ofReal
        ((1 / 2 : ℝ) * leadingOnesVisitedLevelMeanResidence p i) := by
  rw [leadingOnesUniformLevelResidenceContribution_eq_visitMass_mul_mean p i]
  rw [leadingOnesUniformLevelVisitMass_eq_half hp0 hp1 i]
  rw [← ENNReal_ofReal_half]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Total assembled expected residence contribution over all nonterminal LeadingOnes
levels.  This is the probabilistic/algebraic side of the final runtime identity. -/
noncomputable def leadingOnesUniformResidenceContributionTotal
    (n : ℕ) (p : ℝ) : ENNReal :=
  ∑ i : Fin n, leadingOnesUniformLevelResidenceContribution p i

/-- The assembled level-residence contribution is exactly the `ENNReal` embedding of
the real finite-sum runtime formula from Stage 27 fix 11. -/
theorem leadingOnesUniformResidenceContributionTotal_eq_ofReal_formula
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    leadingOnesUniformResidenceContributionTotal n p =
      ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) := by
  classical
  unfold leadingOnesUniformResidenceContributionTotal
  calc
    (∑ i : Fin n, leadingOnesUniformLevelResidenceContribution p i) =
        ∑ i : Fin n,
          ENNReal.ofReal
            ((1 / 2 : ℝ) * leadingOnesVisitedLevelMeanResidence p i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact leadingOnesUniformLevelResidenceContribution_eq_ofReal_half_mean
        hp0 hp1 i
    _ = ENNReal.ofReal
        (∑ i : Fin n,
          (1 / 2 : ℝ) * leadingOnesVisitedLevelMeanResidence p i) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i _hi
      exact mul_nonneg (by norm_num)
        (leadingOnesVisitedLevelMeanResidence_nonneg hp0 hp1 i)
    _ = ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) := by
      unfold leadingOnesUniformExpectedRuntimeFormula
      rw [Finset.mul_sum]

/-- Expanded closed finite-level form of the assembled contribution. -/
theorem leadingOnesUniformResidenceContributionTotal_eq_ofReal_finiteSum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    leadingOnesUniformResidenceContributionTotal n p =
      ENNReal.ofReal
        ((1 / 2 : ℝ) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹) := by
  rw [leadingOnesUniformResidenceContributionTotal_eq_ofReal_formula hp0 hp1]
  rw [leadingOnesUniformExpectedRuntimeFormula_eq]

/-- Once the remaining representation bridge identifies the genuine sample-path
expectation with the assembled residence contribution, the exact runtime formula is an
immediate corollary.  Keeping this implication explicit makes the sole remaining proof
obligation visible in the public API. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_formula_of_bridge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hbridge :
      leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
        leadingOnesUniformResidenceContributionTotal n p) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) := by
  rw [hbridge]
  exact leadingOnesUniformResidenceContributionTotal_eq_ofReal_formula hp0 hp1

end ECRuntime
