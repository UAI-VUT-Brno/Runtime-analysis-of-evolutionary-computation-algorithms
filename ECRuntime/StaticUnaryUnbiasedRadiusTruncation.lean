import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 88: radius truncation under a bounded first moment

The conditional pair-flip estimates used in the corrected linear-runtime proof
involve the *second factorial* radius moment.  A bounded mean radius alone
cannot replace that term.  The first step toward a bounded-mean-only analysis
is therefore to separate short and long mutations **without conditioning on a
flipped coordinate**.

For a cutoff `b`, the theorems below give:

* the unconditional probability of a mutation with radius at least `b` is at
  most `meanRadius / b`;
* the contribution of radii at most `b` to the second factorial moment is at
  most `b * meanRadius`;
* the total second factorial moment splits exactly into those two pieces.

None of these statements bounds the *tail's second factorial moment* by the
first moment.  That is intentionally not claimed: bounding its effect on the
accepted potential change requires a different, acceptance-aware argument.
No independent-bit or radius-tail assumption is made.
-/

/-- Probability mass of radii `k ≥ b` in the finite radius distribution. -/
def radiusTailMass {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if b ≤ k then law.radiusMass k else 0

/-- Second factorial radius moment contributed by radii `k ≤ b`. -/
def truncatedSecondFactorialRadiusMoment {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ≤ b then
      (k : ℝ) * ((k - 1 : ℕ) : ℝ) * law.radiusMass k
    else 0

/-- Second factorial radius moment contributed by radii `k > b`. -/
def tailSecondFactorialRadiusMoment {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ≤ b then 0
    else (k : ℝ) * ((k - 1 : ℕ) : ℝ) * law.radiusMass k

/-- The unconditional tail mass is nonnegative, without a positive-cutoff
hypothesis. -/
theorem radiusTailMass_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    0 ≤ law.radiusTailMass b := by
  unfold radiusTailMass
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact law.radiusMass_nonneg k
  · exact le_refl 0

/-- A multiplication form of the Markov inequality that also handles cutoff
zero; no division by the cutoff occurs in this intermediate result. -/
theorem radiusTailMass_mul_cutoff_le_meanRadius {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    (b : ℝ) * law.radiusTailMass b ≤ law.meanRadius := by
  unfold radiusTailMass meanRadius
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hbk : b ≤ k
  · simp only [if_pos hbk]
    have hcast : (b : ℝ) ≤ (k : ℝ) := by exact_mod_cast hbk
    exact mul_le_mul_of_nonneg_right hcast (law.radiusMass_nonneg k)
  · simp only [if_neg hbk, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg k) (law.radiusMass_nonneg k)

/-- Markov tail inequality for the mutation radius. Under the *first moment*
assumption alone, the probability of a radius at least `b` is at most `χ/b`.
The estimate is unconditional and must not be applied to a size-biased
coordinate-flip conditional distribution without further work. -/
theorem radiusTailMass_le_meanRadius_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) {b : ℕ} (hb : 0 < b) :
    law.radiusTailMass b ≤ law.meanRadius / (b : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  apply (le_div_iff₀ hbR).2
  simpa only [mul_comm] using
    (law.radiusTailMass_mul_cutoff_le_meanRadius b)

/-- The small-radius portion of the factorial second moment is bounded by
`b χ`, using only a finite cutoff and the unconditional first moment.  This
requires no uniform bound on the total second factorial moment. -/
theorem truncatedSecondFactorialRadiusMoment_le_cutoff_mul_meanRadius
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    law.truncatedSecondFactorialRadiusMoment b ≤
      (b : ℝ) * law.meanRadius := by
  unfold truncatedSecondFactorialRadiusMoment meanRadius
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hkb : k ≤ b
  · simp only [if_pos hkb]
    have hkminus : ((k - 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast ((Nat.sub_le k 1).trans hkb)
    have hterm : 0 ≤ (k : ℝ) * law.radiusMass k :=
      mul_nonneg (Nat.cast_nonneg k) (law.radiusMass_nonneg k)
    calc
      (k : ℝ) * ((k - 1 : ℕ) : ℝ) * law.radiusMass k =
          ((k - 1 : ℕ) : ℝ) * ((k : ℝ) * law.radiusMass k) := by ring
      _ ≤ (b : ℝ) * ((k : ℝ) * law.radiusMass k) :=
        mul_le_mul_of_nonneg_right hkminus hterm
  · simp only [if_neg hkb]
    exact mul_nonneg (Nat.cast_nonneg b)
      (mul_nonneg (Nat.cast_nonneg k) (law.radiusMass_nonneg k))

/-- The two factorial-moment pieces are nonnegative, even if `b` lies
outside the radius support. -/
theorem truncatedSecondFactorialRadiusMoment_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    0 ≤ law.truncatedSecondFactorialRadiusMoment b := by
  unfold truncatedSecondFactorialRadiusMoment
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg (k - 1)))
      (law.radiusMass_nonneg k)
  · exact le_refl 0

/-- The large-radius portion of the second factorial moment is nonnegative. -/
theorem tailSecondFactorialRadiusMoment_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    0 ≤ law.tailSecondFactorialRadiusMoment b := by
  unfold tailSecondFactorialRadiusMoment
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg (k - 1)))
      (law.radiusMass_nonneg k)

/-- Exact splitting of the *unconditional* second factorial radius moment.
This is an identity, not an upper bound for the long-radius remainder. It
provides the appropriate starting point for an acceptance-aware tail analysis
without silently using a bounded second moment. -/
theorem secondFactorialRadiusMoment_eq_truncated_add_tail {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    law.secondFactorialRadiusMoment =
      law.truncatedSecondFactorialRadiusMoment b +
        law.tailSecondFactorialRadiusMoment b := by
  unfold secondFactorialRadiusMoment truncatedSecondFactorialRadiusMoment
    tailSecondFactorialRadiusMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkb : k ≤ b
  · simp only [if_pos hkb, add_zero]
  · simp only [if_neg hkb, zero_add]

end StaticUnaryUnbiasedMutation
end ECRuntime
