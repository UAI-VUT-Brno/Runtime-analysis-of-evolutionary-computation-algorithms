import ECRuntime.LeadingOnesExactEntryAveraging
import ECRuntime.LeadingOnesExpectedRuntimeAssembly
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 27 fix 18: exact-runtime closure from the one-level bridge

This small module makes the remaining proof distance explicit.  All global runtime
bookkeeping is already complete: Stage 27 fix 17 rewrites the genuine uniformly
initialized first-hitting-time expectation as the finite sum of genuine score-level
charge expectations, while Stage 27 fix 12 proves that the assembled exact-entry-mass
times mean-residence total is the desired closed formula.

Consequently the full theorem follows from one family of local identities, one for each
`i : Fin n`.  The statements below package that final closure without assuming or
proving the local identity itself.  The next substantive module therefore has only one
mathematical target: identify one genuine score-level charge expectation with the
already defined level residence contribution.
-/

/-- If every genuine score-level expected charge equals the corresponding promoted
entry-mass times mean-residence contribution, then the whole genuine runtime
expectation equals the assembled residence total. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_residenceContributionTotal_of_scoreLevelBridge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlevel : ∀ i : Fin n,
      leadingOnesUniformScoreLevelChargeExpectation n p hp0.le hp1.le i =
        leadingOnesUniformLevelResidenceContribution p i) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      leadingOnesUniformResidenceContributionTotal n p := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_eq_sum_scoreLevelChargeExpectation
    n p hp0.le hp1.le]
  unfold leadingOnesUniformResidenceContributionTotal
  apply Finset.sum_congr rfl
  intro i _hi
  exact hlevel i

/-- The one-level bridge immediately closes the canonical exact finite-`n` expectation
formula. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_formula_of_scoreLevelBridge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlevel : ∀ i : Fin n,
      leadingOnesUniformScoreLevelChargeExpectation n p hp0.le hp1.le i =
        leadingOnesUniformLevelResidenceContribution p i) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) := by
  calc
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
        leadingOnesUniformResidenceContributionTotal n p :=
      leadingOnesUniformFirstHittingTimeExpectation_eq_residenceContributionTotal_of_scoreLevelBridge
        hp0 hp1 hlevel
    _ = ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) :=
      leadingOnesUniformResidenceContributionTotal_eq_ofReal_formula hp0 hp1

/-- Expanded finite-sum form of the same closure theorem. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum_of_scoreLevelBridge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlevel : ∀ i : Fin n,
      leadingOnesUniformScoreLevelChargeExpectation n p hp0.le hp1.le i =
        leadingOnesUniformLevelResidenceContribution p i) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      ENNReal.ofReal
        ((1 / 2 : ℝ) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹) := by
  calc
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
        ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) :=
      leadingOnesUniformFirstHittingTimeExpectation_eq_formula_of_scoreLevelBridge
        hp0 hp1 hlevel
    _ = ENNReal.ofReal
        ((1 / 2 : ℝ) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹) := by
      rw [leadingOnesUniformExpectedRuntimeFormula_eq]

end ECRuntime
