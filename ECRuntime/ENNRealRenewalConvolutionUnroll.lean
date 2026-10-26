import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: reusable algebraic recurrence unrolling in extended nonnegative reals.
The theorem does not assume a Markov property; a genuine one-step
occupation recurrence must be established independently. -/

/-- An ENNReal initial/entry/stay recurrence is its finite entrance-time convolution. -/
theorem proposed_ennreal_oneStepRenewal_eq_finiteConvolution
    (occupation entry : Nat → ENNReal) (q : ENNReal)
    (hzero : occupation 0 = entry 0)
    (hstep : ∀ t, occupation (t + 1) = entry (t + 1) + q * occupation t)
    (t : Nat) :
    occupation t = ∑ k ∈ Finset.range (t + 1), entry k * q ^ (t - k) := by
  induction t with
  | zero =>
      simpa [Finset.sum_range_succ] using hzero
  | succ t ih =>
      have hscale :
          q * (∑ k ∈ Finset.range (t + 1), entry k * q ^ (t - k)) =
            ∑ k ∈ Finset.range (t + 1), entry k * q ^ (t + 1 - k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkt : k < t + 1 := Finset.mem_range.mp hk
        have hexp : t + 1 - k = (t - k) + 1 := by omega
        rw [hexp, pow_succ]
        ac_rfl
      calc
        occupation (t + 1) = entry (t + 1) + q * occupation t := hstep t
        _ = entry (t + 1) + q *
              (∑ k ∈ Finset.range (t + 1), entry k * q ^ (t - k)) := by rw [ih]
        _ = entry (t + 1) +
              (∑ k ∈ Finset.range (t + 1), entry k * q ^ (t + 1 - k)) := by rw [hscale]
        _ = ∑ k ∈ Finset.range (t + 2), entry k * q ^ (t + 1 - k) := by
          conv_rhs => rw [Finset.sum_range_succ]
          simp only [Nat.sub_self, pow_zero, mul_one]
          ac_rfl

end ECRuntime
