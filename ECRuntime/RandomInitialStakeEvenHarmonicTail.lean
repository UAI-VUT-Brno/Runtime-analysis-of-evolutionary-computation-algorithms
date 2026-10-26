import ECRuntime.FitnessLevel
import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 172 — approved candidate: even-parity harmonic bridge

Source direction: Doerr--Doerr, Collecting Coupons with Random Initial Stake.
The verified exact mean is n(H_n - log 2) plus an exponentially small term.
The paper's sharper parity-adjusted expression involves H_(n/2) and an
additive -1/2 correction. This step exposes the finite *even-dimension*
harmonic tail to which the asymptotic trapezoidal estimate must be applied.
It is not the sharper asymptotic theorem itself; odd n and the remainder
bounds remain separate obligations.

The user approved this theorem statement after admission-free elaboration.
The existing public runtime theorems are unchanged pending eight-gate promotion.
-/

/-- The finite harmonic increment from `m` to `2m` is exactly the reciprocal
sum over the upper half. This gives a precise analytic target for the
`-1/2` parity correction, without assuming any asymptotic approximation. -/
theorem proposed_randomInitialStake_evenHarmonicTail (m : ℕ) :
    harmonicReal (2 * m) - harmonicReal m =
      (Finset.Icc (m + 1) (2 * m)).sum (fun j => (j : ℝ)⁻¹) := by
  classical
  have hcast : ∀ r : ℕ,
      harmonicReal r = (Finset.Icc 1 r).sum (fun j => (j : ℝ)⁻¹) := by
    intro r
    simp [harmonicReal, harmonic_eq_sum_Icc]
  have hsubset : (Finset.Icc 1 m) ⊆ (Finset.Icc 1 (2 * m)) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hdiff :
      (Finset.Icc 1 (2 * m)) \ (Finset.Icc 1 m) =
        Finset.Icc (m + 1) (2 * m) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hsplit := Finset.sum_sdiff
    (f := fun j : ℕ => (j : ℝ)⁻¹) hsubset
  rw [hdiff] at hsplit
  rw [hcast (2 * m), hcast m]
  linarith

end ECRuntime
