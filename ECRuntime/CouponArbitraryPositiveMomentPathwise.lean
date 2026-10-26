import Mathlib

namespace ECRuntime

/-! P02: all positive integer truncated moments admit one telescoping
survival-indicator identity. Unlike a formal power-series statement,
this requires only finite sums and no convergence assumption. -/

/-- Pathwise truncated power identity for every strictly positive exponent. -/
theorem proposed_coupon_truncatedPositivePower_tailIndicators
    (horizon hit exponent : Nat) :
    ((min horizon hit : Nat) : Real) ^ (exponent + 1) =
      Finset.sum (Finset.range horizon) (fun k =>
        if k < hit then
          (((k + 1 : Nat) : Real) ^ (exponent + 1) -
            (k : Real) ^ (exponent + 1)) else 0) := by
  have htel (m : Nat) :
      ((m : Nat) : Real) ^ (exponent + 1) =
        Finset.sum (Finset.range m) (fun k =>
          (((k + 1 : Nat) : Real) ^ (exponent + 1) -
            (k : Real) ^ (exponent + 1))) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, <- ih]
        ring
  rw [htel (min horizon hit)]
  rw [<- Finset.sum_filter]
  congr 1
  ext k
  simp

end ECRuntime
