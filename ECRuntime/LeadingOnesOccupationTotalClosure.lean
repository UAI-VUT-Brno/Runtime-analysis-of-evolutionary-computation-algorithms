import ECRuntime.LeadingOnesExactStayBranch
import ECRuntime.LeadingOnesLevelChargeOccupation
import Mathlib

open scoped BigOperators ENNReal
open Finset

namespace ECRuntime

/-!
# Stage 27 fix 24 fix 3: total occupation mass and exact LeadingOnes runtime closure

Stage 27 fix 23 fix 3 is compiler verified warning/error-free.  The first fix-24
compiler round reached this final analytic module and exposed only two proof/API issues: a
reflexive entry-`tsum` goal left open after unfolding, and use of a generic topological-semiring
Cauchy-product theorem that is not applicable to `ENNReal`.  Fix 24 fix 1 closed the reflexive
goal and moved the Cauchy product to native `ENNReal` `tsum` lemmas, but the compiler
then exposed a name collision: `Finset.antidiagonal` resolves to the newer PWO-based
construction in Mathlib 4.32.1. Fix 24 fix 2 explicitly selected the natural additive
antidiagonal from `Finset.Nat.instHasAntidiagonal`, but its final nested-`tsum` flattening
attempted to rewrite `ENNReal.tsum_sigma'` directly inside a dependent double sum and did
not match the target. Fix 24 fix 3 first converts the double antidiagonal sum to an explicit
sigma-type `tsum`, then reindexes that sigma sum with `Equiv.tsum_eq`. The analytic argument
and theorem statements are unchanged.  The stochastic part of
one fixed score level is now complete: exact-time occupation mass is the finite
convolution of exact first-entry mass with powers of the exact stay probability.

This file performs the remaining nonnegative countable-sum calculation.  Because all
quantities live in `ENNReal`, every relevant family is summable.  We use the native
`ENNReal` `tsum` API together with the natural antidiagonal decomposition of `ℕ × ℕ`,
so no topological-semiring instance is required.  Summing the verified finite convolution gives

  total occupation
    = (eventual exact-entry mass) * (geometric stay-tail sum).

The geometric factor is the already promoted exact mean residence.  This discharges the
fixed-initial occupation bridge used by Stage 27 fix 19 and therefore closes the genuine
uniformly initialized finite-`n` LeadingOnes expectation formula.
-/

/-- The monotone partial-sum definition of fixed-initial total occupation is the
ordinary `ENNReal` time `tsum`. -/
theorem leadingOnesFixedInitialScoreLevelOccupationTotal_eq_tsum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) :
    leadingOnesFixedInitialScoreLevelOccupationTotal
        p hp0 hp1 x i =
      ∑' t : ℕ,
        leadingOnesFixedInitialScoreLevelOccupationMass
          p hp0 hp1 x i t := by
  unfold leadingOnesFixedInitialScoreLevelOccupationTotal
  rw [ENNReal.tsum_eq_iSup_nat]

/-- The `tsum` of the packaged exact-entry masses is exactly the previously defined
fixed-initial eventual exact-entry mass. -/
theorem tsum_leadingOnesFixedInitialExactEntryENNMass_eq_eventual
    {n : ℕ} (p : ℝ) (i : Fin n) (x : BitString n) :
    (∑' t : ℕ, leadingOnesFixedInitialExactEntryENNMass p i x t) =
      leadingOnesFixedInitialEventualExactEntryMass p i x := by
  unfold leadingOnesFixedInitialExactEntryENNMass
  unfold leadingOnesFixedInitialEventualExactEntryMass
  rfl

/-- Native `ENNReal` Cauchy product on natural-indexed nonnegative series, expressed
through finite antidiagonals.  This avoids the `IsTopologicalSemiring` hypothesis of the
generic topological-semiring Cauchy-product theorem, which `ENNReal` intentionally does
not satisfy. -/
private theorem ennreal_tsum_cauchy_nat (f g : ℕ → ENNReal) :
    (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) =
      (∑' s : ℕ, f s) * (∑' k : ℕ, g k) := by
  calc
    (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) =
        ∑' n : ℕ, ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n, f ij.1 * g ij.2 := by
      apply tsum_congr
      intro n
      exact
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun s k => f s * g k) n).symm
    _ = ∑' n : ℕ, ∑' ij : ↥(Finset.Nat.instHasAntidiagonal.antidiagonal n), f ij.1.1 * g ij.1.2 := by
      apply tsum_congr
      intro n
      exact
        (Finset.tsum_subtype
          (Finset.Nat.instHasAntidiagonal.antidiagonal n) (fun ij : ℕ × ℕ => f ij.1 * g ij.2)).symm
    _ = ∑' q : (Σ n : ℕ, ↥(Finset.Nat.instHasAntidiagonal.antidiagonal n)),
          f ((q.2 : ℕ × ℕ).1) * g ((q.2 : ℕ × ℕ).2) := by
      exact
        (ENNReal.tsum_sigma'
          (fun q : (Σ n : ℕ, ↥(Finset.Nat.instHasAntidiagonal.antidiagonal n)) =>
            f ((q.2 : ℕ × ℕ).1) * g ((q.2 : ℕ × ℕ).2))).symm
    _ = ∑' ij : ℕ × ℕ, f ij.1 * g ij.2 := by
      have h :=
        ((Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd :
          (Σ n : ℕ, ↥(Finset.Nat.instHasAntidiagonal.antidiagonal n)) ≃ ℕ × ℕ).tsum_eq
            (fun ij : ℕ × ℕ => f ij.1 * g ij.2))
      simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply] at h
      exact h
    _ = ∑' s : ℕ, ∑' k : ℕ, f s * g k := by
      exact ENNReal.tsum_prod (f := fun s k => f s * g k)
    _ = ∑' s : ℕ, f s * (∑' k : ℕ, g k) := by
      apply tsum_congr
      intro s
      exact ENNReal.tsum_mul_left
    _ = (∑' s : ℕ, f s) * (∑' k : ℕ, g k) := by
      exact ENNReal.tsum_mul_right

/-- Summing the compiler-promoted finite entry/stay convolution over all times is the
Cauchy product of the eventual-entry series and the geometric stay series. -/
theorem tsum_leadingOnesFixedInitialScoreLevelOccupationMass_eq_entry_mul_stayTsum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) :
    (∑' t : ℕ,
        leadingOnesFixedInitialScoreLevelOccupationMass
          p hp0 hp1 x i t) =
      (∑' s : ℕ, leadingOnesFixedInitialExactEntryENNMass p i x s) *
        (∑' k : ℕ, (leadingOnesLevelStayENNReal p i) ^ k) := by
  calc
    (∑' t : ℕ,
        leadingOnesFixedInitialScoreLevelOccupationMass
          p hp0 hp1 x i t) =
        ∑' t : ℕ,
          ∑ s ∈ Finset.range (t + 1),
            leadingOnesFixedInitialExactEntryENNMass p i x s *
              (leadingOnesLevelStayENNReal p i) ^ (t - s) := by
      apply tsum_congr
      intro t
      exact leadingOnesFixedInitialScoreLevelOccupationMass_eq_entryConvolution
        p hp0 hp1 x i t
    _ =
      (∑' s : ℕ, leadingOnesFixedInitialExactEntryENNMass p i x s) *
        (∑' k : ℕ, (leadingOnesLevelStayENNReal p i) ^ k) := by
      exact
        ennreal_tsum_cauchy_nat
          (fun s : ℕ => leadingOnesFixedInitialExactEntryENNMass p i x s)
          (fun k : ℕ => (leadingOnesLevelStayENNReal p i) ^ k)

/-- The `ENNReal` geometric stay series is the promoted exact real mean residence,
embedded in `ENNReal`. -/
theorem tsum_leadingOnesLevelStayENNReal_pow_eq_ofReal_meanResidence
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    (∑' k : ℕ, (leadingOnesLevelStayENNReal p i) ^ k) =
      ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) := by
  have hq0 : 0 < leadingOnesLevelExitProbability p i :=
    leadingOnesLevelExitProbability_pos hp0 hp1 i
  have hq1 : leadingOnesLevelExitProbability p i ≤ 1 :=
    leadingOnesLevelExitProbability_le_one hp0 hp1 i
  have hstay0 : 0 ≤ 1 - leadingOnesLevelExitProbability p i := by
    linarith
  have hone_sub :
      1 - leadingOnesLevelStayENNReal p i =
        ENNReal.ofReal (leadingOnesLevelExitProbability p i) := by
    unfold leadingOnesLevelStayENNReal
    calc
      1 - ENNReal.ofReal (1 - leadingOnesLevelExitProbability p i) =
          ENNReal.ofReal (1 : ℝ) -
            ENNReal.ofReal (1 - leadingOnesLevelExitProbability p i) := by
        norm_num
      _ = ENNReal.ofReal
          ((1 : ℝ) - (1 - leadingOnesLevelExitProbability p i)) := by
        exact (ENNReal.ofReal_sub (1 : ℝ) hstay0).symm
      _ = ENNReal.ofReal (leadingOnesLevelExitProbability p i) := by
        congr 1
        ring
  calc
    (∑' k : ℕ, (leadingOnesLevelStayENNReal p i) ^ k) =
        (1 - leadingOnesLevelStayENNReal p i)⁻¹ :=
      ENNReal.tsum_geometric (leadingOnesLevelStayENNReal p i)
    _ = (ENNReal.ofReal (leadingOnesLevelExitProbability p i))⁻¹ := by
      rw [hone_sub]
    _ = ENNReal.ofReal ((leadingOnesLevelExitProbability p i)⁻¹) := by
      exact (ENNReal.ofReal_inv_of_pos hq0).symm
    _ = ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) := by
      rfl

/-- Fixed-initial total score-level occupation is exactly eventual exact-entry mass
multiplied by the exact mean residence.  This is the final local bridge required by the
global exact-runtime closure. -/
theorem leadingOnesFixedInitialScoreLevelOccupationTotal_eq_eventualExactEntry_mul_meanResidence
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (x : BitString n) (i : Fin n) :
    leadingOnesFixedInitialScoreLevelOccupationTotal
        p hp0.le hp1.le x i =
      leadingOnesFixedInitialEventualExactEntryMass p i x *
        ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i) := by
  rw [leadingOnesFixedInitialScoreLevelOccupationTotal_eq_tsum
    p hp0.le hp1.le x i]
  rw [tsum_leadingOnesFixedInitialScoreLevelOccupationMass_eq_entry_mul_stayTsum
    p hp0.le hp1.le x i]
  rw [tsum_leadingOnesFixedInitialExactEntryENNMass_eq_eventual p i x]
  rw [tsum_leadingOnesLevelStayENNReal_pow_eq_ofReal_meanResidence hp0 hp1 i]

/-- Unconditional one-level exact charge/residence bridge for the genuine uniformly
initialized LeadingOnes trajectory. -/
theorem leadingOnesUniformScoreLevelChargeExpectation_eq_residenceContribution
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesUniformScoreLevelChargeExpectation
        n p hp0.le hp1.le i =
      leadingOnesUniformLevelResidenceContribution p i := by
  apply
    leadingOnesUniformScoreLevelChargeExpectation_eq_residenceContribution_of_fixedOccupationBridge
      hp0 hp1 i
  intro x
  exact
    leadingOnesFixedInitialScoreLevelOccupationTotal_eq_eventualExactEntry_mul_meanResidence
      hp0 hp1 x i

/-- Main exact finite-`n` LeadingOnes expectation theorem in the canonical formula
wrapper. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_formula
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      ENNReal.ofReal (leadingOnesUniformExpectedRuntimeFormula n p) := by
  apply leadingOnesUniformFirstHittingTimeExpectation_eq_formula_of_scoreLevelBridge
    hp0 hp1
  intro i
  exact leadingOnesUniformScoreLevelChargeExpectation_eq_residenceContribution
    hp0 hp1 i

/-- Expanded finite-level form of the exact finite-`n` LeadingOnes expectation. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      ENNReal.ofReal
        ((1 / 2 : ℝ) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹) := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_eq_formula hp0 hp1]
  rw [leadingOnesUniformExpectedRuntimeFormula_eq]

end ECRuntime
