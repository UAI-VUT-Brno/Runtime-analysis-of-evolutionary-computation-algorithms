import ECRuntime.Mutation
import Mathlib

namespace ECRuntime

/-!
# Stage 28: scaled standard-bit mutation rates

The transition and mutation layers of `ECRuntime` already support an arbitrary real
bit-mutation probability `p`.  What was still missing from the literature roadmap was
one canonical spelling for the asymptotically important regime `p = c/n`.

This module supplies that spelling with the same explicit zero-dimensional convention
as `standardMutationRate`, proves the elementary admissibility facts needed by runtime
theorems, and relates the new rate to the existing repository-wide standard rate.
No stochastic or runtime argument is introduced here.
-/

/-- Scaled standard-bit mutation rate `c/n`, with the zero-dimensional case separated. -/
noncomputable def scaledMutationRate (c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else c / (n : ℝ)

@[simp] theorem scaledMutationRate_zero (c : ℝ) :
    scaledMutationRate c 0 = 0 := by
  simp [scaledMutationRate]

/-- In positive dimension, the scaled rate is literally `c/n`. -/
theorem scaledMutationRate_eq_div_of_pos
    {c : ℝ} {n : ℕ} (hn : 0 < n) :
    scaledMutationRate c n = c / (n : ℝ) := by
  simp [scaledMutationRate, Nat.ne_of_gt hn]

/-- The `c=1` scaled rate is exactly the repository-wide standard mutation rate. -/
theorem scaledMutationRate_one_eq_standardMutationRate (n : ℕ) :
    scaledMutationRate 1 n = standardMutationRate n := by
  by_cases hn : n = 0
  · subst n
    simp [scaledMutationRate, standardMutationRate]
  · simp [scaledMutationRate, standardMutationRate, hn, div_eq_mul_inv]

/-- In positive dimension, `c/n` is `c` times the standard mutation rate. -/
theorem scaledMutationRate_eq_mul_standardMutationRate
    {c : ℝ} {n : ℕ} (hn : 0 < n) :
    scaledMutationRate c n = c * standardMutationRate n := by
  rw [scaledMutationRate_eq_div_of_pos hn]
  simp [standardMutationRate, Nat.ne_of_gt hn, div_eq_mul_inv]

/-- Positive scale gives a positive mutation rate in positive dimension. -/
theorem scaledMutationRate_pos
    {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 0 < n) :
    0 < scaledMutationRate c n := by
  rw [scaledMutationRate_eq_div_of_pos hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact div_pos hc hnR

/-- Nonnegative scale gives a nonnegative mutation rate. -/
theorem scaledMutationRate_nonneg
    {c : ℝ} {n : ℕ} (hc : 0 ≤ c) :
    0 ≤ scaledMutationRate c n := by
  by_cases hn : n = 0
  · subst n
    simp [scaledMutationRate]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [scaledMutationRate_eq_div_of_pos hnpos]
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    exact div_nonneg hc hnR

/-- If `c < n`, then the scaled rate is strictly below one. -/
theorem scaledMutationRate_lt_one
    {c : ℝ} {n : ℕ} (hn : 0 < n) (hcn : c < (n : ℝ)) :
    scaledMutationRate c n < 1 := by
  rw [scaledMutationRate_eq_div_of_pos hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  calc
    c / (n : ℝ) < (n : ℝ) / (n : ℝ) :=
      (div_lt_div_iff_of_pos_right hnR).2 hcn
    _ = 1 := div_self (ne_of_gt hnR)

/-- If `c ≤ n`, then the scaled rate is at most one. -/
theorem scaledMutationRate_le_one
    {c : ℝ} {n : ℕ} (hn : 0 < n) (hcn : c ≤ (n : ℝ)) :
    scaledMutationRate c n ≤ 1 := by
  rw [scaledMutationRate_eq_div_of_pos hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  calc
    c / (n : ℝ) ≤ (n : ℝ) / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnR).2 hcn
    _ = 1 := div_self (ne_of_gt hnR)

/-- A convenient admissibility package for the nondegenerate `p=c/n` regime. -/
theorem scaledMutationRate_mem_unitInterval
    {c : ℝ} {n : ℕ} (hc : 0 ≤ c) (hn : 0 < n) (hcn : c ≤ (n : ℝ)) :
    0 ≤ scaledMutationRate c n ∧ scaledMutationRate c n ≤ 1 := by
  exact ⟨scaledMutationRate_nonneg hc, scaledMutationRate_le_one hn hcn⟩

/-- A convenient strict admissibility package for exact-runtime results. -/
theorem scaledMutationRate_mem_openUnitInterval
    {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 0 < n) (hcn : c < (n : ℝ)) :
    0 < scaledMutationRate c n ∧ scaledMutationRate c n < 1 := by
  exact ⟨scaledMutationRate_pos hc hn, scaledMutationRate_lt_one hn hcn⟩

end ECRuntime
