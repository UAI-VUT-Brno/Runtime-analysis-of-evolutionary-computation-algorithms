import ECRuntime.LeadingOnesOccupationTotalClosure
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 255 (P01, new proposal): extract an explicit ENNReal Cauchy product
for a level-dependent arrival mass and its geometric stay tail. All functions
are arbitrary nonnegative ENNReal sequences. This is a reusable algebraic
component of the missing Stage-245 occupation argument, NOT its probabilistic
finite-history convolution assumption.
-/

/-- Total nonnegative occupation convolution factors into the eventual
entry mass and the aggregate stay tail. -/
theorem proposed_adaptive_occupation_tsum_entryStay_convolution
    (entry stay : Nat → ENNReal) :
    (∑' t : Nat, ∑ s ∈ Finset.range (t + 1), entry s * stay (t - s)) =
      (∑' s : Nat, entry s) * (∑' k : Nat, stay k) := by
  calc
    (∑' t : Nat, ∑ s ∈ Finset.range (t + 1), entry s * stay (t - s)) =
        ∑' t : Nat, ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal t,
          entry ij.1 * stay ij.2 := by
      apply tsum_congr
      intro t
      exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun s k => entry s * stay k) t).symm
    _ = ∑' t : Nat,
        ∑' ij : ↥(Finset.Nat.instHasAntidiagonal.antidiagonal t),
          entry ij.1.1 * stay ij.1.2 := by
      apply tsum_congr
      intro t
      exact (Finset.tsum_subtype
        (Finset.Nat.instHasAntidiagonal.antidiagonal t)
        (fun ij : Nat × Nat => entry ij.1 * stay ij.2)).symm
    _ = ∑' q : (Σ t : Nat, ↥(Finset.Nat.instHasAntidiagonal.antidiagonal t)),
          entry ((q.2 : Nat × Nat).1) * stay ((q.2 : Nat × Nat).2) := by
      exact (ENNReal.tsum_sigma'
        (fun q : (Σ t : Nat, ↥(Finset.Nat.instHasAntidiagonal.antidiagonal t)) =>
          entry ((q.2 : Nat × Nat).1) * stay ((q.2 : Nat × Nat).2))).symm
    _ = ∑' ij : Nat × Nat, entry ij.1 * stay ij.2 := by
      have h :=
        ((Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd :
          (Σ t : Nat, ↥(Finset.Nat.instHasAntidiagonal.antidiagonal t)) ≃ Nat × Nat).tsum_eq
            (fun ij : Nat × Nat => entry ij.1 * stay ij.2))
      simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply] at h
      exact h
    _ = ∑' s : Nat, ∑' k : Nat, entry s * stay k := by
      exact ENNReal.tsum_prod (f := fun s k => entry s * stay k)
    _ = ∑' s : Nat, entry s * (∑' k : Nat, stay k) := by
      apply tsum_congr
      intro s
      exact ENNReal.tsum_mul_left
    _ = (∑' s : Nat, entry s) * (∑' k : Nat, stay k) := by
      exact ENNReal.tsum_mul_right

end ECRuntime
