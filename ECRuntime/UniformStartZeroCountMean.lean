import ECRuntime.BitString
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 136 — promoted after the complete Round 22 eight-gate verification.
A reusable finite combinatorial identity recording that a uniformly sampled
bitstring has on average n/2 zero coordinates. This is the averaging lemma
under the uniform-start survival estimate of Stage 135; the identity is
independent of any optimizer or mutation operator.
-/

/-- The average number of zero coordinates among all length-n bitstrings
is precisely half the dimension. -/
theorem proposed_bitStrings_uniformAverage_zeroCount_eq_half (n : Nat) :
    (Finset.univ.sum (fun x : BitString n => (zeroCount x : Real))) /
      (2 : Real) ^ n = (n : Real) / 2 := by
  classical
  -- Bitwise complementation exchanges zero and one coordinates and is an involution.
  let toggle : BitString n ≃ BitString n :=
    { toFun := fun x i => !(x i)
      invFun := fun x i => !(x i)
      left_inv := by
        intro x
        funext i
        simp only [Bool.not_not]
      right_inv := by
        intro x
        funext i
        simp only [Bool.not_not] }
  have htoggle (x : BitString n) :
      zeroCount x = oneCount (toggle x) := by
    unfold zeroCount oneCount
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hzeroOne :
      (∑ x : BitString n, (zeroCount x : Real)) =
        (∑ x : BitString n, (oneCount x : Real)) := by
    refine Fintype.sum_equiv toggle
      (fun x : BitString n => (zeroCount x : Real))
      (fun x : BitString n => (oneCount x : Real)) ?_
    intro x
    exact congrArg (fun k : Nat => (k : Real)) (htoggle x)
  have htotal :
      (∑ x : BitString n,
        ((zeroCount x : Real) + (oneCount x : Real))) =
        (n : Real) * (2 : Real) ^ n := by
    calc
      _ = ∑ _x : BitString n, (n : Real) := by
        apply Finset.sum_congr rfl
        intro x _
        exact_mod_cast (by simpa only [add_comm] using
          (oneCount_add_zeroCount x) : zeroCount x + oneCount x = n)
      _ = (n : Real) * (2 : Real) ^ n := by
        simp; ring
  have htwice :
      (2 : Real) * (∑ x : BitString n, (zeroCount x : Real)) =
        (n : Real) * (2 : Real) ^ n := by
    rw [Finset.sum_add_distrib, ← hzeroOne] at htotal
    linarith
  have hden : (2 : Real) ^ n ≠ 0 := by positivity
  rw [div_eq_iff hden]
  linarith

end ECRuntime
