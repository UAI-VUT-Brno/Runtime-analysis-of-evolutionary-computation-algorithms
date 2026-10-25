import ECRuntime.RandomInitialStakeEvenHarmonicTail
import Mathlib

namespace ECRuntime

/-!
Stage 191, new statement requiring human approval.

The exact correction in the random-initial-stake theorem reduces to the tail
of the positive sequence

  d_j = 1 / ((2*j+1)*(2*j+2)).

For positive j the sequence has a *telescoping* comparison with
  (4*(j+1)*(j+2))^{-1} and (4*j*(j+1))^{-1}.
The key remaining analytic obligation is to identify log 2 as the limit of
the finite alternating-pair harmonic sums. This candidate does NOT assume
that identity, and does not purport to prove the Stage 189 sandwich.
-/

/-- Elementary real-algebra comparison of the three positive denominators. -/
private theorem stage191_denominator_bounds (x : Real) (hx : 1 ≤ x) :
    (4 * x * (x+1)) ≤ ((2*x+1) * (2*x+2)) ∧
      ((2*x+1) * (2*x+2)) ≤ (4 * (x+1) * (x+2)) := by
  constructor <;> nlinarith

/-- Each dyadic pair is trapped between adjacent telescoping terms.
Unlike the Stage 189 limit, this is a purely rational inequality. -/
theorem proposed_randomInitialStake_pairReciprocalBounds
    (j : Nat) (hj : 1 ≤ j) :
    1 / (4 * ((j : Real) + 1) * ((j : Real) + 2)) ≤
      1 / ((2 * (j : Real) + 1) * (2 * (j : Real) + 2)) ∧
    1 / ((2 * (j : Real) + 1) * (2 * (j : Real) + 2)) ≤
      1 / (4 * (j : Real) * ((j : Real) + 1)) := by
  have hx : (1 : Real) ≤ (j : Real) := by exact_mod_cast hj
  obtain ⟨hupperDen, hlowerDen⟩ := stage191_denominator_bounds (j : Real) hx
  have hleft : (0 : Real) < 4 * ((j : Real)+1) * ((j : Real)+2) := by positivity
  have hmid : (0 : Real) < (2 * (j : Real)+1) * (2 * (j : Real)+2) := by positivity
  have hright : (0 : Real) < 4 * (j : Real) * ((j : Real)+1) := by positivity
  constructor
  · exact (div_le_div_iff₀ hleft hmid).2 (by nlinarith)
  · exact (div_le_div_iff₀ hmid hright).2 (by nlinarith)

/-- The dyadic pair is exactly the positive reciprocal-quadratic summand. -/
theorem stage191_dyadicPair_eq_reciprocal (j : Nat) :
    (((2*j+1 : Nat) : Real)⁻¹ - ((2*j+2 : Nat) : Real)⁻¹) =
      1 / ((2 * (j : Real)+1) * (2 * (j : Real)+2)) := by
  have h1 : (((2*j+1 : Nat) : Real)) = 2 * (j : Real)+1 := by
    push_cast
    ring
  have h2 : (((2*j+2 : Nat) : Real)) = 2 * (j : Real)+2 := by
    push_cast
    ring
  rw [h1, h2]
  have hn1 : (2 * (j : Real)+1) ≠ 0 := by positivity
  have hn2 : (2 * (j : Real)+2) ≠ 0 := by positivity
  field_simp [hn1, hn2]
  ring

end ECRuntime
