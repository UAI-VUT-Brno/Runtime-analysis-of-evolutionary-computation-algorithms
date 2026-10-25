import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesResidenceGeometricSeries
import Mathlib

namespace ECRuntime

/-!
# Stage 178 (P01): locally optimal adaptive mutation probability

The paper-level theorem is approved and its header is frozen. The previous
proof only established the first three levels. This round replaces the
remaining admission with a general *weighted arithmetic--geometric mean*
argument. The proof had six redundant ring tactics removed after proof-10 elaboration; certification is decided
by the pinned Lean checker, not by algebraic testing.

For a level i > 0, put a=i+1, b=i and apply weighted AM--GM to
  z1=a*p, z2=(a/b)*(1-p), w1=1/a, w2=b/a.
The weighted arithmetic mean is p+(1-p)=1, whence
  (a*p)*((a/b)*(1-p))^i <= 1.
Multiplying by (b/a)^i/a proves the desired exit-rate bound.
The endpoint i=0 follows from p<=1. No suffix-bit visitation assertion
or globally optimal adaptive policy is inferred here.
-/

/-- Weighted two-term AM--GM specialized to the local LeadingOnes exit mass. -/
private theorem stage178_exitOptimality_amgm
    (i : Nat) (hi : 0 < i) (p : Real) (hp0 : 0 <= p) (hp1 : p <= 1) :
    p * (1 - p) ^ i <=
      (((i + 1 : Nat) : Real)⁻¹) *
        (1 - (((i + 1 : Nat) : Real)⁻¹)) ^ i := by
  let a : Real := ((i + 1 : Nat) : Real)
  let b : Real := (i : Real)
  let z1 : Real := a * p
  let z2 : Real := a * (1 - p) / b
  let w1 : Real := a⁻¹
  let w2 : Real := b / a
  let r : Real := b / a
  have hb : 0 < b := by
    change (0 : Real) < (i : Real)
    exact_mod_cast hi
  have ha : a = b + 1 := by
    dsimp [a, b]
    push_cast
    ring
  have ha0 : 0 < a := by linarith
  have han : a ≠ 0 := ne_of_gt ha0
  have hbn : b ≠ 0 := ne_of_gt hb
  have hz1 : 0 <= z1 := by
    dsimp [z1]
    exact mul_nonneg ha0.le hp0
  have hz2 : 0 <= z2 := by
    dsimp [z2]
    exact div_nonneg (mul_nonneg ha0.le (by linarith)) hb.le
  have hw1 : 0 <= w1 := inv_nonneg.mpr ha0.le
  have hw2 : 0 <= w2 := div_nonneg hb.le ha0.le
  have hw_sum : w1 + w2 = 1 := by
    change a⁻¹ + b / a = 1
    rw [div_eq_mul_inv]
    calc
      a⁻¹ + b * a⁻¹ = (b + 1) * a⁻¹ := by ring
      _ = a * a⁻¹ := by rw [ha]
      _ = 1 := mul_inv_cancel₀ han
  have hwz1 : w1 * z1 = p := by
    change a⁻¹ * (a * p) = p
    field_simp [han]
  have hwz2 : w2 * z2 = 1 - p := by
    change b / a * (a * (1 - p) / b) = 1 - p
    field_simp [han, hbn]
  have hAM : z1 ^ w1 * z2 ^ w2 <= 1 := by
    have h := Real.geom_mean_le_arith_mean2_weighted
      hw1 hw2 hz1 hz2 hw_sum
    rw [hwz1, hwz2] at h
    linarith
  have hw1_mul : w1 * ((i + 1 : Nat) : Real) = 1 := by
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ han
  have hw2_mul : w2 * ((i + 1 : Nat) : Real) = (i : Real) := by
    change b / a * a = b
    field_simp [han]
  have hz1_pow : (z1 ^ w1) ^ (i + 1) = z1 := by
    calc
      (z1 ^ w1) ^ (i + 1) = z1 ^ (w1 * ((i + 1 : Nat) : Real)) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_mul hz1 w1 ((i + 1 : Nat) : Real)).symm
      _ = z1 := by rw [hw1_mul]; simp
  have hz2_pow : (z2 ^ w2) ^ (i + 1) = z2 ^ i := by
    calc
      (z2 ^ w2) ^ (i + 1) = z2 ^ (w2 * ((i + 1 : Nat) : Real)) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_mul hz2 w2 ((i + 1 : Nat) : Real)).symm
      _ = z2 ^ i := by rw [hw2_mul, Real.rpow_natCast]
  have hprod_nonneg : 0 <= z1 ^ w1 * z2 ^ w2 :=
    mul_nonneg (Real.rpow_nonneg hz1 _) (Real.rpow_nonneg hz2 _)
  have hAMpow := pow_le_pow_left₀ hprod_nonneg hAM (i + 1)
  have hAMnat : z1 * z2 ^ i <= 1 := by
    simpa only [mul_pow, one_pow, hz1_pow, hz2_pow] using hAMpow
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
  have hscale : 0 <= r ^ i / a :=
    div_nonneg (pow_nonneg hrpos.le i) ha0.le
  have hscaled := mul_le_mul_of_nonneg_right hAMnat hscale
  have hleft : z1 * z2 ^ i * (r ^ i / a) = p * (1 - p) ^ i := by
    calc
      z1 * z2 ^ i * (r ^ i / a) = (z1 / a) * (z2 * r) ^ i := by
        rw [mul_pow]
        ring
      _ = p * (1 - p) ^ i := by rw [hz1div, hz2r]
  have hright : r ^ i / a = a⁻¹ * (1 - a⁻¹) ^ i := by
    rw [hrform]
    ring
  calc
    p * (1 - p) ^ i = z1 * z2 ^ i * (r ^ i / a) := hleft.symm
    _ <= 1 * (r ^ i / a) := hscaled
    _ = a⁻¹ * (1 - a⁻¹) ^ i := by rw [one_mul, hright]
    _ = (((i + 1 : Nat) : Real)⁻¹) *
          (1 - (((i + 1 : Nat) : Real)⁻¹)) ^ i := by rfl

/-- The geometric local exit mass p(1-p)^i is maximized at 1/(i+1).
This statement includes the i=0 endpoint case and is valid without an
assumption that the corresponding score level is actually visited. -/
theorem proposed_leadingOnesAdaptive_localExitOptimality
    (i : Nat) (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) ^ i ≤
      (((i + 1 : Nat) : Real)⁻¹) *
        (1 - (((i + 1 : Nat) : Real)⁻¹)) ^ i := by
  by_cases hi : i = 0
  · subst i
    simpa using hp1
  · exact stage178_exitOptimality_amgm i (Nat.pos_of_ne_zero hi) p hp0 hp1

end ECRuntime
