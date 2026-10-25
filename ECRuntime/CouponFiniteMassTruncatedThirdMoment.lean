import ECRuntime.CouponTruncatedCubeSurvivalIndicators
import Mathlib

namespace ECRuntime

/-! P02: finite Fubini for third truncated moments of arbitrary signed
masses. No stochastic assumptions or convergence exchange are needed. -/

/-- A finite signed third moment is a quadratic-weighted survival sum. -/
theorem proposed_coupon_finiteMass_truncatedThirdMoment_tailSum
    (horizon : Nat) (mass : Nat -> Real) :
    Finset.sum (Finset.range (horizon + 1))
      (fun t => mass t * ((min horizon t : Nat) : Real) ^ 3) =
    Finset.sum (Finset.range horizon)
      (fun k => ((3 * k * k + 3 * k + 1 : Nat) : Real) *
        Finset.sum (Finset.range (horizon + 1))
          (fun t => if k < t then mass t else 0)) := by
  classical
  have hCube (t : Nat) :
      ((min horizon t : Nat) : Real) ^ 3 =
      Finset.sum (Finset.range horizon)
        (fun k => if k < t then ((3 * k * k + 3 * k + 1 : Nat) : Real) else 0) := by
    exact_mod_cast (proposed_coupon_truncatedCube_eq_survivalIndicators horizon t)
  calc
    Finset.sum (Finset.range (horizon + 1))
        (fun t => mass t * ((min horizon t : Nat) : Real) ^ 3) =
      Finset.sum (Finset.range (horizon + 1))
        (fun t => Finset.sum (Finset.range horizon)
          (fun k => mass t *
            (if k < t then ((3 * k * k + 3 * k + 1 : Nat) : Real) else 0))) := by
              apply Finset.sum_congr rfl
              intro t _
              rw [hCube t, Finset.mul_sum]
    _ = Finset.sum (Finset.range horizon)
        (fun k => Finset.sum (Finset.range (horizon + 1))
          (fun t => mass t *
            (if k < t then ((3 * k * k + 3 * k + 1 : Nat) : Real) else 0))) := by
              rw [Finset.sum_comm]
    _ = Finset.sum (Finset.range horizon)
        (fun k => ((3 * k * k + 3 * k + 1 : Nat) : Real) *
          Finset.sum (Finset.range (horizon + 1))
            (fun t => if k < t then mass t else 0)) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              split_ifs <;> ring

end ECRuntime
