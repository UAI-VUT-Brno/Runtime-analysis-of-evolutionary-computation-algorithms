import ECRuntime.AdaptiveLeadingOnesLocalOptimalRate
import Mathlib

namespace ECRuntime

/-! P01: equality-case strengthening of the certified weighted AM--GM
bound. The rate p=1/(j+1) is the unique maximizing point for j>0.
The endpoint j=0 must not be included in an interior uniqueness claim. -/

/-- Equality in the local exit-mass inequality forces the optimal rate. -/
theorem proposed_leadingOnes_positiveLevelExit_uniqueMaximizer
    (j : Nat) (hj : 0 < j) (p : Real)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (heq : p * (1 - p) ^ j =
       (1 / ((j + 1 : Nat) : Real)) *
         (1 - 1 / ((j + 1 : Nat) : Real)) ^ j) :
    p = 1 / ((j + 1 : Nat) : Real) := by
  -- Reuse the same weighted AM--GM normalization as certified Stage 178,
  -- but apply Mathlib's equality characterization for *positive* weights.
  let a : Real := ((j + 1 : Nat) : Real)
  let b : Real := (j : Real)
  let z1 : Real := a * p
  let z2 : Real := a * (1 - p) / b
  let w1 : Real := a⁻¹
  let w2 : Real := b / a
  let r : Real := b / a
  have hb : 0 < b := by
    change (0 : Real) < (j : Real)
    exact_mod_cast hj
  have ha : a = b + 1 := by
    dsimp [a, b]
    push_cast
    ring
  have ha0 : 0 < a := by linarith
  have han : a ≠ 0 := ne_of_gt ha0
  have hbn : b ≠ 0 := ne_of_gt hb
  have hz1 : 0 <= z1 := mul_nonneg ha0.le hp0
  have hz2 : 0 <= z2 := by
    dsimp [z2]
    exact div_nonneg (mul_nonneg ha0.le (by linarith)) hb.le
  have hw1 : 0 < w1 := by
    exact inv_pos.mpr ha0
  have hw2 : 0 < w2 := div_pos hb ha0
  have hw_sum : w1 + w2 = 1 := by
    change a⁻¹ + b / a = 1
    rw [div_eq_mul_inv]
    calc
      a⁻¹ + b * a⁻¹ = (b + 1) * a⁻¹ := by ring
      _ = a * a⁻¹ := by rw [ha]
      _ = 1 := mul_inv_cancel₀ han
  have hwz1 : w1 * z1 = p := by
    change a⁻¹ * (a * p) = p
    simp [han]
  have hwz2 : w2 * z2 = 1 - p := by
    change b / a * (a * (1 - p) / b) = 1 - p
    field_simp [han, hbn]
  have hw1_mul : w1 * ((j + 1 : Nat) : Real) = 1 := by
    change a⁻¹ * a = 1
    simp [han]
  have hw2_mul : w2 * ((j + 1 : Nat) : Real) = (j : Real) := by
    change b / a * a = b
    field_simp [han]
  have hz1_pow : (z1 ^ w1) ^ (j + 1) = z1 := by
    calc
      (z1 ^ w1) ^ (j + 1) =
          z1 ^ (w1 * ((j + 1 : Nat) : Real)) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_mul hz1 w1 ((j + 1 : Nat) : Real)).symm
      _ = z1 := by rw [hw1_mul]; simp
  have hz2_pow : (z2 ^ w2) ^ (j + 1) = z2 ^ j := by
    calc
      (z2 ^ w2) ^ (j + 1) =
          z2 ^ (w2 * ((j + 1 : Nat) : Real)) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_mul hz2 w2 ((j + 1 : Nat) : Real)).symm
      _ = z2 ^ j := by rw [hw2_mul, Real.rpow_natCast]
  have hprod_nonneg : 0 <= z1 ^ w1 * z2 ^ w2 :=
    mul_nonneg (Real.rpow_nonneg hz1 _) (Real.rpow_nonneg hz2 _)
  have hrpos : 0 < r := div_pos hb ha0
  have hrform : r = 1 - a⁻¹ := by
    change b / a = 1 - a⁻¹
    have hba : b = a - 1 := by linarith
    rw [hba]
    field_simp [han]
  have hz2r : z2 * r = 1 - p := by
    change (a * (1 - p) / b) * (b / a) = 1 - p
    field_simp [han, hbn]
  have hz1div : z1 / a = p := by
    change a * p / a = p
    field_simp [han]
  have hleft : z1 * z2 ^ j * (r ^ j / a) = p * (1 - p) ^ j := by
    calc
      z1 * z2 ^ j * (r ^ j / a) = (z1 / a) * (z2 * r) ^ j := by
        rw [mul_pow]
        ring
      _ = p * (1 - p) ^ j := by rw [hz1div, hz2r]
  have hright : r ^ j / a = a⁻¹ * (1 - a⁻¹) ^ j := by
    rw [hrform]
    ring
  have hEq : p * (1 - p) ^ j =
      a⁻¹ * (1 - a⁻¹) ^ j := by
    change p * (1 - p) ^ j = (1 / a) * (1 - 1 / a) ^ j at heq
    simpa only [one_div] using heq
  have hcpos : 0 < r ^ j / a :=
    div_pos (pow_pos hrpos _) ha0
  have hunit : z1 * z2 ^ j = 1 := by
    apply mul_right_cancel₀ (ne_of_gt hcpos)
    calc
      (z1 * z2 ^ j) * (r ^ j / a) = p * (1 - p) ^ j := hleft
      _ = a⁻¹ * (1 - a⁻¹) ^ j := hEq
      _ = 1 * (r ^ j / a) := by rw [hright]; ring
  have hprod_pow : (z1 ^ w1 * z2 ^ w2) ^ (j + 1) =
      (1 : Real) ^ (j + 1) := by
    rw [mul_pow, hz1_pow, hz2_pow, hunit, one_pow]
  have hprod_eq : z1 ^ w1 * z2 ^ w2 = 1 :=
    (pow_left_inj₀ hprod_nonneg (by norm_num : (0 : Real) <= 1)
      (by omega : j + 1 ≠ 0)).mp hprod_pow
  have hmean_eq : z1 ^ w1 * z2 ^ w2 = w1 * z1 + w2 * z2 := by
    rw [hprod_eq, hwz1, hwz2]
    ring
  have hz_eq : z1 = z2 :=
    (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
      hw1 hw2 hz1 hz2 hw_sum).mp hmean_eq
  have hbp : b * p = 1 - p := by
    apply mul_left_cancel₀ han
    calc
      a * (b * p) = b * (a * p) := by ring
      _ = b * (a * (1 - p) / b) := by exact congrArg (fun t => b * t) hz_eq
      _ = a * (1 - p) := by field_simp [hbn]
  have hap : a * p = 1 := by
    rw [ha]
    nlinarith [hbp]
  change p = 1 / a
  apply (eq_div_iff han).2
  nlinarith [hap]

end ECRuntime
