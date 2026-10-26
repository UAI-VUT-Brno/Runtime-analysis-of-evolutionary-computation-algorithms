import ECRuntime.CouponArbitraryPositiveMomentPathwise
import Mathlib

namespace ECRuntime

/-! P02: a finite Fubini theorem upgrades the pathwise arbitrary positive
integer moment identity to arbitrary signed atomic masses. No probabilistic
independence or monotone convergence is required. -/

/-- Finite signed truncated moments are weighted survival-tail sums for
all strictly positive integer exponents. -/
theorem proposed_coupon_finiteMass_truncatedPower_tailSum
    (horizon exponent : Nat) (mass : Nat -> Real) :
    Finset.sum (Finset.range (horizon + 1)) (fun t =>
      mass t * ((min horizon t : Nat) : Real) ^ (exponent + 1)) =
    Finset.sum (Finset.range horizon) (fun k =>
      ((((k + 1 : Nat) : Real) ^ (exponent + 1) -
         (k : Real) ^ (exponent + 1))) *
        Finset.sum (Finset.range (horizon + 1))
          (fun t => if k < t then mass t else 0)) := by
  classical
  have hpower (t : Nat) :
      ((min horizon t : Nat) : Real) ^ (exponent + 1) =
      Finset.sum (Finset.range horizon) (fun k =>
        if k < t then
          (((k + 1 : Nat) : Real) ^ (exponent + 1) -
            (k : Real) ^ (exponent + 1)) else 0) :=
    proposed_coupon_truncatedPositivePower_tailIndicators horizon t exponent
  calc
    _ = Finset.sum (Finset.range (horizon + 1)) (fun t =>
      Finset.sum (Finset.range horizon) (fun k =>
        mass t * (if k < t then
          (((k + 1 : Nat) : Real) ^ (exponent + 1) -
            (k : Real) ^ (exponent + 1)) else 0))) := by
       apply Finset.sum_congr rfl
       intro t _
       rw [hpower t, Finset.mul_sum]
    _ = Finset.sum (Finset.range horizon) (fun k =>
      Finset.sum (Finset.range (horizon + 1)) (fun t =>
        mass t * (if k < t then
          (((k + 1 : Nat) : Real) ^ (exponent + 1) -
            (k : Real) ^ (exponent + 1)) else 0))) := by
       rw [Finset.sum_comm]
    _ = _ := by
       apply Finset.sum_congr rfl
       intro k _
       rw [Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro t _
       split_ifs <;> ring

end ECRuntime
