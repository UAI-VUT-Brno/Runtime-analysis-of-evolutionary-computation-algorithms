import ECRuntime.CouponPathwiseTruncatedSquareIndicators
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P02: finite Fubini bridge required before identifying actual
squared hitting times of a finite Markov trajectory. This statement is
about an arbitrary signed finite mass function, so does not smuggle in
an unstated hitting-time distribution or absorption assumption. -/

/-- Discrete truncated second moments are odd-weighted survival-mass sums. -/
theorem proposed_coupon_finiteMass_truncatedSecondMoment_tailSum
    (horizon : Nat) (mass : Nat → Real) :
    (∑ t ∈ Finset.range (horizon + 1),
       mass t * ((min horizon t : Nat) : Real) ^ 2) =
    (∑ k ∈ Finset.range horizon,
       ((2 * k + 1 : Nat) : Real) *
         ∑ t ∈ Finset.range (horizon + 1),
           if k < t then mass t else 0) := by
  classical
  have hSquare (t : Nat) :
      ((min horizon t : Nat) : Real) ^ 2 =
      Finset.sum (Finset.range horizon)
        (fun k => if k < t then ((2 * k + 1 : Nat) : Real) else 0) := by
    have hNat :
        (min horizon t) ^ 2 =
        Finset.sum (Finset.range horizon)
          (fun k => if k < t then (2 * k + 1 : Nat) else 0) := by
      simpa only [pow_two] using
        (proposed_coupon_truncatedSquare_eq_survivalIndicators horizon t)
    exact_mod_cast hNat
  calc
    Finset.sum (Finset.range (horizon + 1))
        (fun t => mass t * ((min horizon t : Nat) : Real) ^ 2) =
      Finset.sum (Finset.range (horizon + 1))
        (fun t => Finset.sum (Finset.range horizon)
          (fun k => mass t *
            (if k < t then ((2 * k + 1 : Nat) : Real) else 0))) := by
              apply Finset.sum_congr rfl
              intro t _
              rw [hSquare t, Finset.mul_sum]
    _ = Finset.sum (Finset.range horizon)
        (fun k => Finset.sum (Finset.range (horizon + 1))
          (fun t => mass t *
            (if k < t then ((2 * k + 1 : Nat) : Real) else 0))) := by
              rw [Finset.sum_comm]
    _ = Finset.sum (Finset.range horizon)
        (fun k => ((2 * k + 1 : Nat) : Real) *
          Finset.sum (Finset.range (horizon + 1))
            (fun t => if k < t then mass t else 0)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              split_ifs <;> ring

end ECRuntime
