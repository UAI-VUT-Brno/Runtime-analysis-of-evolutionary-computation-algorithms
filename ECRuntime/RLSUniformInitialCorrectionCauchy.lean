import ECRuntime.RLSUniformInitialCorrectionTail
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 146 — user-approved statement; promoted after the complete Round 29 gate; compiler-observed declaration pinned in Round29PromotionPins. Source direction: Doerr--Doerr (2013), collecting coupons with a random
initial stake. Exact finite modulus of the correction sequence, obtained from
the fully promoted Stage 145 tail estimate. The modulus implies the
sequence is Cauchy; it does not identify the limit with log 2.
-/

private noncomputable def stage146_correction (n : Nat) : Real :=
  (Finset.Icc 1 n).sum (fun j =>
    (1 : Real) / ((j : Real) * (2 : Real) ^ j))

/-- Each dimension adds exactly one correction summand. -/
private theorem stage146_correction_succ (k : Nat) :
    stage146_correction (k + 1) = stage146_correction k +
      (1 : Real) / (((k + 1 : Nat) : Real) * (2 : Real) ^ (k + 1)) := by
  have hout : k + 1 ∉ Finset.Icc 1 k := by simp
  have hIcc : Finset.Icc 1 (k + 1) =
      insert (k + 1) (Finset.Icc 1 k) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  simp only [stage146_correction, hIcc, Finset.sum_insert hout]
  ring

/-- The difference between two partial corrections equals their tail,
including the empty interval when the upper and lower indices coincide. -/
private theorem stage146_difference_eq_tail (n d : Nat) :
    stage146_correction (n + d) - stage146_correction n =
      (Finset.Icc (n + 1) (n + d)).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hout : n + d + 1 ∉ Finset.Icc (n + 1) (n + d) := by simp
      have hIcc : Finset.Icc (n + 1) (n + (d + 1)) =
          insert (n + d + 1) (Finset.Icc (n + 1) (n + d)) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      -- Rewrite the finite interval first: normalizing n+(d+1)
      -- beforehand erases the exact index expression in hIcc.
      rw [hIcc, Finset.sum_insert hout]
      rw [show n + (d + 1) = n + d + 1 by omega,
        stage146_correction_succ]
      linarith [ih]

/-- Uniform finite Cauchy modulus for the half-geometric harmonic
correction, with no asymptotic or log-series assumption. -/
theorem proposed_rlsUniformInitial_harmonicCorrection_cauchyModulus
    (n m : Nat) (h : n ≤ m) :
    0 ≤ (Finset.Icc 1 m).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) -
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ∧
    (Finset.Icc 1 m).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) -
      (Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤
      (1 : Real) / (2 : Real) ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  change 0 ≤ stage146_correction (n + d) - stage146_correction n ∧
    stage146_correction (n + d) - stage146_correction n ≤
      (1 : Real) / (2 : Real) ^ n
  rw [stage146_difference_eq_tail]
  exact proposed_rlsUniformInitial_harmonicCorrection_tailBound n (n + d) (by omega)

end ECRuntime
