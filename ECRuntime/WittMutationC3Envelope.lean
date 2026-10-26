import ECRuntime.WittMutationCaseC3
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Generic finite C3-envelope infrastructure

This module contains endpoint-independent facts about the finite C3 envelope.  Earlier
versions kept these lemmas inside the first numerical extension module, which made every
later endpoint depend on the complete history of rational certificates.  They now live at
the abstraction boundary where they belong: new endpoint proofs need only import this file
and provide a certificate at their right endpoint.
-/

/-- The exact C3 envelope is downward closed in the mutation probability on `[0,1)`. -/
theorem wittMutationC3EnvelopeCondition_mono
    {n : ℕ} {p q : ℝ}
    (hp0 : 0 ≤ p) (hq1 : q < 1) (hpq : p ≤ q)
    (henv : WittMutationC3EnvelopeCondition q n) :
    WittMutationC3EnvelopeCondition p n := by
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq1
  have hq0 : 0 ≤ q := hp0.trans hpq
  have hbase : wittMutationBase p ≤ wittMutationBase q :=
    wittMutationBase_mono hp1 hq1 hpq
  have hsum0 :
      0 ≤ ∑ i : Fin n, wittMutationBase p ^ i.val := by
    apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (wittMutationBase_pos hp1).le _
  have hsumle :
      (∑ i : Fin n, wittMutationBase p ^ i.val) ≤
        ∑ i : Fin n, wittMutationBase q ^ i.val := by
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (wittMutationBase_pos hp1).le hbase i.val
  unfold WittMutationC3EnvelopeCondition at henv ⊢
  calc
    p * (∑ i : Fin n, wittMutationBase p ^ i.val) ≤
        q * (∑ i : Fin n, wittMutationBase p ^ i.val) :=
      mul_le_mul_of_nonneg_right hpq hsum0
    _ ≤ q * (∑ i : Fin n, wittMutationBase q ^ i.val) :=
      mul_le_mul_of_nonneg_left hsumle hq0
    _ ≤ 2 := henv

/-- The scaled mutation rate is monotone in the scale parameter in positive dimension. -/
theorem scaledMutationRate_mono_scale
    {n : ℕ} (hn : 0 < n) {c d : ℝ} (hcd : c ≤ d) :
    scaledMutationRate c n ≤ scaledMutationRate d n := by
  rw [scaledMutationRate_eq_mul_standardMutationRate hn,
    scaledMutationRate_eq_mul_standardMutationRate hn]
  have hstd0 : 0 ≤ standardMutationRate n := by
    rw [standardMutationRate, if_neg (Nat.ne_of_gt hn)]
    positivity
  exact mul_le_mul_of_nonneg_right hcd hstd0

/-- A right-endpoint C3 certificate extends to every nonnegative smaller scale. -/
theorem wittMutationC3EnvelopeCondition_scaled_of_endpoint
    {n : ℕ} (hn : 0 < n) {c C : ℝ}
    (hc0 : 0 ≤ c) (hcC : c ≤ C) (hC_lt_n : C < (n : ℝ))
    (hCenv : WittMutationC3EnvelopeCondition (scaledMutationRate C n) n) :
    WittMutationC3EnvelopeCondition (scaledMutationRate c n) n := by
  have hq1 : scaledMutationRate C n < 1 := scaledMutationRate_lt_one hn hC_lt_n
  have hpq : scaledMutationRate c n ≤ scaledMutationRate C n :=
    scaledMutationRate_mono_scale hn hcC
  exact wittMutationC3EnvelopeCondition_mono
    (scaledMutationRate_nonneg hc0) hq1 hpq hCenv

end ECRuntime
