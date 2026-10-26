import ECRuntime.FitnessLevel
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 173 -- proposed odd-parity random-stake harmonic bridge

Source direction: Doerr--Doerr, *Collecting Coupons with Random Initial
Stake*. The finer `n H_{n/2} - 1/2 + o(1)` statement requires careful odd
parity handling. Stage 172 treats the even-dimensional upper-half harmonic
sum. This independently checkable odd case isolates the extra terminal
reciprocal without changing the definition of the published half-index
harmonic convention.

The user approved this theorem header after the previous candidate-only Lean
elaboration. The source remains outside the public import tree until it
passes the complete transitive-axiom and eight-gate promotion checks.
-/

/-- The odd-dimensional harmonic tail is the even upper-half tail plus the
terminal reciprocal. This is an exact finite identity, not an asymptotic
`-1/2` estimate. -/
theorem proposed_randomInitialStake_oddHarmonicTail (m : ℕ) :
    harmonicReal (2 * m + 1) - harmonicReal m =
      (Finset.Icc (m + 1) (2 * m)).sum (fun j => (j : ℝ)⁻¹) +
        ((2 * m + 1 : ℕ) : ℝ)⁻¹ := by
  classical
  have hcast : ∀ r : ℕ,
      harmonicReal r = (Finset.Icc 1 r).sum (fun j => (j : ℝ)⁻¹) := by
    intro r
    simp [harmonicReal, harmonic_eq_sum_Icc]
  have hsubset : Finset.Icc 1 m ⊆ Finset.Icc 1 (2 * m) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hdiff :
      (Finset.Icc 1 (2 * m)) \ (Finset.Icc 1 m) =
        Finset.Icc (m + 1) (2 * m) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have heven : harmonicReal (2 * m) - harmonicReal m =
      (Finset.Icc (m + 1) (2 * m)).sum (fun j => (j : ℝ)⁻¹) := by
    have hs := Finset.sum_sdiff
      (f := fun j : ℕ => (j : ℝ)⁻¹) hsubset
    rw [hdiff] at hs
    rw [hcast (2 * m), hcast m]
    linarith
  have hsucc : harmonicReal (2 * m + 1) =
      harmonicReal (2 * m) + ((2 * m + 1 : ℕ) : ℝ)⁻¹ := by
    simp [harmonicReal, harmonic_succ]
  rw [hsucc]
  linarith

end ECRuntime
