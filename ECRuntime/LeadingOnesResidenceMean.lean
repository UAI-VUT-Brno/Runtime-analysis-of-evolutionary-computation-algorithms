import ECRuntime.LeadingOnesResidence
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 27 fix 11: exact mean residence at a visited LeadingOnes level

Stage 27 fix 10 compiler-verifies the exact finite survival law at every visited
LeadingOnes level `i`:

  `finiteLevelSurvival ... k x = (1 - q_i)^k`,

where `q_i = p * (1-p)^i` is the exact one-step probability of leaving the level.
This file performs the next analytic step only.  It sums the verified survival profile
and identifies the tail-sum mean residence with `q_i⁻¹` under `0 < p < 1`.

The resulting theorem is the local expectation ingredient needed for the final runtime
assembly.  The whole-process expected runtime is intentionally not identified here;
the next slice can combine these per-level means with the already promoted uniform
visit mass `1/2` and the sample-path level-charge decomposition.
-/

/-- A positive geometric success probability at most one has survival-tail sum equal
its reciprocal.  This is the real tail-sum identity used for exact residence means. -/
theorem tsum_geometric_survival_eq_inv
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑' k : ℕ, (1 - q) ^ k) = q⁻¹ := by
  have hr0 : 0 ≤ 1 - q := by linarith
  have hr1 : 1 - q < 1 := by linarith
  calc
    (∑' k : ℕ, (1 - q) ^ k) = (1 - (1 - q))⁻¹ :=
      tsum_geometric_of_lt_one hr0 hr1
    _ = q⁻¹ := by ring_nf

/-- The exact LeadingOnes level-exit probability is strictly positive in the
nondegenerate mutation regime. -/
theorem leadingOnesLevelExitProbability_pos
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    0 < leadingOnesLevelExitProbability p i := by
  unfold leadingOnesLevelExitProbability
  have hq : 0 < 1 - p := by linarith
  positivity

/-- The exact LeadingOnes level-exit probability is at most one. -/
theorem leadingOnesLevelExitProbability_le_one
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesLevelExitProbability p i ≤ 1 := by
  unfold leadingOnesLevelExitProbability
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ i.val ≤ 1 := pow_le_one₀ hq0 hq1
  calc
    p * (1 - p) ^ i.val ≤ p * 1 :=
      mul_le_mul_of_nonneg_left hpow hp0.le
    _ = p := by ring
    _ ≤ 1 := hp1.le

/-- Hence the corresponding one-step stay probability belongs to `[0,1)`. -/
theorem leadingOnesLevelStayProbability_mem_Ico
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    0 ≤ 1 - leadingOnesLevelExitProbability p i ∧
      1 - leadingOnesLevelExitProbability p i < 1 := by
  have hpos := leadingOnesLevelExitProbability_pos hp0 hp1 i
  have hle := leadingOnesLevelExitProbability_le_one hp0 hp1 i
  constructor <;> linarith

/-- The exact tail-sum mean residence at a visited LeadingOnes level is the reciprocal
of its exact exit probability.  The left-hand side is the sum of the compiler-promoted
finite survival probabilities from Stage 27 fix 10. -/
theorem tsum_finiteLevelSurvival_leadingOnes_exact
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (i : Fin n) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    (∑' k : ℕ,
        finiteLevelSurvival
          (onePlusOneTransition p (leadingOnesReal (n := n)))
          ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
          k x) =
      leadingOnesVisitedLevelMeanResidence p i := by
  classical
  calc
    (∑' k : ℕ,
        finiteLevelSurvival
          (onePlusOneTransition p (leadingOnesReal (n := n)))
          ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
          k x) =
        ∑' k : ℕ, (1 - leadingOnesLevelExitProbability p i) ^ k := by
      apply tsum_congr
      intro k
      unfold leadingOnesLevelExitProbability
      exact finiteLevelSurvival_leadingOnes_exact
        hp0.le hp1.le i k x hlevel
    _ = (leadingOnesLevelExitProbability p i)⁻¹ :=
      tsum_geometric_survival_eq_inv
        (leadingOnesLevelExitProbability_pos hp0 hp1 i)
        (leadingOnesLevelExitProbability_le_one hp0 hp1 i)
    _ = leadingOnesVisitedLevelMeanResidence p i := by
      rfl

/-- Closed form of the promoted per-level mean residence. -/
theorem leadingOnesVisitedLevelMeanResidence_eq
    {n : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesVisitedLevelMeanResidence p i =
      (p * (1 - p) ^ i.val)⁻¹ := by
  rfl

/-- Algebraic candidate for the uniformly initialized expected LeadingOnes runtime.
The next slice must identify this finite level sum with the actual sample-path expected
optimization time; this definition itself makes no such probabilistic claim. -/
noncomputable def leadingOnesUniformExpectedRuntimeFormula
    (n : ℕ) (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i : Fin n, leadingOnesVisitedLevelMeanResidence p i

/-- Expanded finite-level form of the candidate exact runtime formula. -/
theorem leadingOnesUniformExpectedRuntimeFormula_eq
    (n : ℕ) (p : ℝ) :
    leadingOnesUniformExpectedRuntimeFormula n p =
      (1 / 2 : ℝ) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹ := by
  unfold leadingOnesUniformExpectedRuntimeFormula
  apply congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

end ECRuntime
