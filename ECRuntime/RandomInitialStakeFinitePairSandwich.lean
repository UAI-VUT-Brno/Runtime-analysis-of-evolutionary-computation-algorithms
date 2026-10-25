import ECRuntime.RandomInitialStakePairTailBounds
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 196 (PROPOSED, unapproved): sum the certified Stage 191 dyadic
reciprocal-pair comparison over an arbitrary finite shifted tail. This
intermediate result does not identify the infinite tail with `log 2`; that
separate analytic step is supplied by the Stage 193 limit candidate.
-/

/-- The finite tail of dyadic reciprocal pairs lies between the two
shifted telescoping rational sums. -/
theorem proposed_randomInitialStake_finitePairTail_sandwich
    (m n : Nat) (hm : 1 ≤ m) :
    (Finset.range n).sum (fun j =>
      1 / (4 * (((m + j : Nat) : Real) + 1) *
        (((m + j : Nat) : Real) + 2))) ≤
      (Finset.range n).sum (fun j =>
        1 / ((2 * ((m + j : Nat) : Real) + 1) *
          (2 * ((m + j : Nat) : Real) + 2))) ∧
    (Finset.range n).sum (fun j =>
        1 / ((2 * ((m + j : Nat) : Real) + 1) *
          (2 * ((m + j : Nat) : Real) + 2))) ≤
      (Finset.range n).sum (fun j =>
        1 / (4 * ((m + j : Nat) : Real) *
          (((m + j : Nat) : Real) + 1))) := by
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    have hidx : 1 ≤ m + j := by omega
    exact (proposed_randomInitialStake_pairReciprocalBounds (m + j) hidx).1
  · apply Finset.sum_le_sum
    intro j hj
    have hidx : 1 ≤ m + j := by omega
    exact (proposed_randomInitialStake_pairReciprocalBounds (m + j) hidx).2

end ECRuntime
