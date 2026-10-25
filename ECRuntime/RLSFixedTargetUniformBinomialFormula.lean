import ECRuntime.RLSFixedTargetAllInitialStates
import ECRuntime.RLSRandomStart
import ECRuntime.BinomialHarmonicAverageClosedForm
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 260 (P07): approved exact finite target from a uniformly random start.
This closes the formerly admitted combinatorial step using the certified
zero-count fibre cardinality `bitStrings_zeroCount_card_eq_choose`.
The lemma below has no probabilistic assumptions: all probability semantics
are discharged by the separately certified Stage 257 pointwise identity.
-/

/-- Uniformly summing any real-valued function of the number of zero bits
is exactly its binomially weighted finite sum. -/
private theorem stage260_sum_by_zeroCount (n : Nat) (f : Nat → Real) :
    (∑ x : BitString n, f (zeroCount x)) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : Real) * f k := by
  classical
  calc
    (∑ x : BitString n, f (zeroCount x)) =
      ∑ x : BitString n,
        ∑ k ∈ Finset.range (n + 1),
          if zeroCount x = k then f k else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        have hx : zeroCount x ∈ Finset.range (n + 1) :=
          Finset.mem_range.mpr (by have h := zeroCount_le x; omega)
        simp [hx]
    _ = ∑ k ∈ Finset.range (n + 1),
          ∑ x : BitString n, if zeroCount x = k then f k else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : Real) * f k := by
        apply Finset.sum_congr rfl
        intro k _hk
        calc
          (∑ x : BitString n, if zeroCount x = k then f k else 0) =
              ∑ x ∈ Finset.univ.filter
                (fun x : BitString n => zeroCount x = k), f k := by
                  rw [Finset.sum_filter]
          _ = ((Finset.univ.filter
                (fun x : BitString n => zeroCount x = k)).card : Real) * f k := by
                  rw [Finset.sum_const, nsmul_eq_mul]
          _ = (Nat.choose n k : Real) * f k := by
                  rw [bitStrings_zeroCount_card_eq_choose]

/-- Genuine uniform-start RLS fixed-target expectation is a binomially
weighted truncated harmonic sum; there is no initial-state restriction. -/
theorem proposed_rlsLinear_fixedTarget_uniformBinomialRuntime
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (r : Nat) :
    ((Fintype.card (BitString n) : Real)⁻¹) *
      (∑ x : BitString n,
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal) =
    ((Fintype.card (BitString n) : Real)⁻¹) *
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : Real) *
          (if k ≤ r then 0
           else (n : Real) * (harmonicReal k - harmonicReal r))) := by
  classical
  have hsum :
      (∑ x : BitString n,
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : Real) *
            (if k ≤ r then 0
             else (n : Real) * (harmonicReal k - harmonicReal r)) := by
    calc
      (∑ x : BitString n,
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal) =
        ∑ x : BitString n,
          if zeroCount x ≤ r then 0
          else (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact proposed_rlsLinear_fixedTarget_runtimeReal_allInitialStates
              hn w hw r x
      _ = ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : Real) *
            (if k ≤ r then 0
             else (n : Real) * (harmonicReal k - harmonicReal r)) := by
            exact stage260_sum_by_zeroCount n (fun k =>
              if k ≤ r then 0
              else (n : Real) * (harmonicReal k - harmonicReal r))
  exact congrArg
    (fun z : Real => ((Fintype.card (BitString n) : Real)⁻¹) * z) hsum

end ECRuntime
