import Mathlib
namespace ECRuntime

/-! Stage 120 promotion candidate: the optimal fixed mutation rate for the Jump_k
plateau escape event. Proof uses two-point weighted AM--GM and does not
conflate the plateau escape phase with total optimization time. -/

/-- Conditional escape probability p^k(1-p)^(n-k) is maximal at k/n. -/
theorem candidateJumpEscape_fixedRate_optimal
    (n k : Nat) (hk : 0 < k) (hkn : k < n)
    (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ k * (1 - p) ^ (n - k) ≤
      ((k : Real) / (n : Real)) ^ k *
        (1 - (k : Real) / (n : Real)) ^ (n - k) := by
  have hn : 0 < n := lt_trans hk hkn
  have hkn : k ≤ n := le_of_lt hkn
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hn0 : (n : Real) ≠ 0 := ne_of_gt hnReal
  let a : Real := (k : Real) / (n : Real)
  let b : Real := ((n - k : Nat) : Real) / (n : Real)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by exact_mod_cast hk) hnReal
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (by exact_mod_cast (show 0 < n - k by omega)) hnReal
  have hab : a + b = 1 := by
    have hsum : k + (n - k) = n := by omega
    have hcast : (k : Real) + ((n - k : Nat) : Real) = (n : Real) := by
      exact_mod_cast hsum
    dsimp [a, b]
    rw [← add_div, hcast]
    exact div_self hn0
  have hb_eq : b = 1 - a := by linarith
  have han : a * (n : Real) = (k : Real) := by
    dsimp [a]
    field_simp [hn0]
  have hbn : b * (n : Real) = ((n - k : Nat) : Real) := by
    dsimp [b]
    field_simp [hn0]
  have hnonneg1 : 0 ≤ p / a := div_nonneg hp0 ha.le
  have hnonneg2 : 0 ≤ (1 - p) / b :=
    div_nonneg (sub_nonneg.mpr hp1) hb.le
  have hmean : a * (p / a) + b * ((1 - p) / b) = 1 := by
    field_simp [ha.ne', hb.ne']
    ring
  have hamgm :
      (p / a) ^ a * ((1 - p) / b) ^ b ≤ 1 := by
    calc
      (p / a) ^ a * ((1 - p) / b) ^ b ≤
          a * (p / a) + b * ((1 - p) / b) :=
        Real.geom_mean_le_arith_mean2_weighted
          ha.le hb.le hnonneg1 hnonneg2 hab
      _ = 1 := hmean
  have hpow_a : ((p / a) ^ a) ^ n = (p / a) ^ k := by
    rw [← Real.rpow_mul_natCast hnonneg1 a n, han, Real.rpow_natCast]
  have hpow_b : (((1 - p) / b) ^ b) ^ n =
      ((1 - p) / b) ^ (n - k) := by
    rw [← Real.rpow_mul_natCast hnonneg2 b n, hbn, Real.rpow_natCast]
  have hratio_le :
      (p / a) ^ k * ((1 - p) / b) ^ (n - k) ≤ 1 := by
    have hbase : 0 ≤ (p / a) ^ a * ((1 - p) / b) ^ b :=
      mul_nonneg (Real.rpow_nonneg hnonneg1 _) (Real.rpow_nonneg hnonneg2 _)
    have hpow := pow_le_pow_left₀ hbase hamgm n
    rw [mul_pow, hpow_a, hpow_b, one_pow] at hpow
    exact hpow
  have hratio :
      (p / a) ^ k * ((1 - p) / b) ^ (n - k) =
      (p ^ k * (1 - p) ^ (n - k)) /
        (a ^ k * b ^ (n - k)) := by
    calc
      (p / a) ^ k * ((1 - p) / b) ^ (n - k) =
          (p ^ k / a ^ k) * ((1 - p) ^ (n - k) / b ^ (n - k)) := by
        simp only [div_pow]
      _ = (p ^ k * (1 - p) ^ (n - k)) /
          (a ^ k * b ^ (n - k)) := by ring
  have hdenpos : 0 < a ^ k * b ^ (n - k) := by positivity
  have hmain : p ^ k * (1 - p) ^ (n - k) ≤
      a ^ k * b ^ (n - k) := by
    apply (div_le_one hdenpos).mp
    rw [← hratio]
    exact hratio_le
  calc
    p ^ k * (1 - p) ^ (n - k) ≤ a ^ k * b ^ (n - k) := hmain
    _ = ((k : Real) / (n : Real)) ^ k *
        (1 - (k : Real) / (n : Real)) ^ (n - k) := by
      rw [hb_eq]

end ECRuntime
