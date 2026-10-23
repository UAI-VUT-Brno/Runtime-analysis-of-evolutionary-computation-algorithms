import ECRuntime.RLSLinearExact
import ECRuntime.RLSRandomStart
import Mathlib

namespace ECRuntime

/-!
Stage 134 — user-approved, provisional public promotion candidate. This is the expected
number of mutation iterations from a uniformly random starting bitstring
for one-bit RLS on any strictly positive linear objective. It combines
the deterministic-start exact runtime (Stage 109) with the certified
finite binomial averaging identity (Stage 110), and corresponds to the
random-initial-stake coupon-collector result of Doerr and Doerr (2013).
The source quantity is `runtimeSup`, which counts mutation iterations,
not the initial fitness evaluation. This is NOT the sharper asymptotic
correction `-1/2 + o(1)`; that remains deferred.
-/

/-- Uniform-start exact RLS expected runtime, averaged over all `2^n`
bitstrings and expressed as a binomial harmonic sum. -/
theorem proposed_rlsLinear_uniformInitial_runtimeAverage
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal) /
        (2 : Real) ^ n =
      ((n : Real) / (2 : Real) ^ n) *
        (Finset.sum (Finset.range (n + 1))
          (fun k => (Nat.choose n k : Real) * harmonicReal k))) := by
  classical
  have hsum :
      (Finset.univ.sum (fun x : BitString n =>
          (runtimeSup
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
              (linearFitness w))
            ({allOnes n} : Set (BitString n)) x).toReal)) =
        Finset.univ.sum (fun x : BitString n =>
          (n : Real) * harmonicReal (zeroCount x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [rlsLinear_runtimeSup_eq_harmonic hn w hw x]
    exact ENNReal.toReal_ofReal
      (mul_nonneg (Nat.cast_nonneg n) (harmonicReal_nonneg (zeroCount x)))
  rw [hsum]
  exact rlsLinear_uniformInitial_harmonic_average n

end ECRuntime
