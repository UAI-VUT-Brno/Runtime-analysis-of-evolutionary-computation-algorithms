import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-! P07: reusable mask-level clipping bound for arbitrary OneMax
thresholds. This makes no independent-bit or one-bit assumption. -/

/-- Replacing the zero count by its excess above a threshold cannot
increase the decrease caused by one accepted elitist mutation. -/
theorem proposed_oneMax_clippedZeroCount_selectedDecrease_le_raw
    {n : Nat} (x : BitString n) (mask : MutationMask n) (k : Nat) :
    (((zeroCount x - k : Nat) : Real) -
       ((zeroCount (selectedAfterMask oneMaxReal x mask) - k : Nat) : Real)) ≤
      ((zeroCount x : Real) -
        (zeroCount (selectedAfterMask oneMaxReal x mask) : Real)) := by
  have hm := oneMaxPotential_selectedAfterMask_le x mask
  change zeroCount (selectedAfterMask oneMaxReal x mask) ≤ zeroCount x at hm
  have hnat :
      zeroCount x - k + zeroCount (selectedAfterMask oneMaxReal x mask) ≤
        zeroCount (selectedAfterMask oneMaxReal x mask) - k + zeroCount x := by
    omega
  have hreal :
      ((zeroCount x - k : Nat) : Real) +
        (zeroCount (selectedAfterMask oneMaxReal x mask) : Real) ≤
      ((zeroCount (selectedAfterMask oneMaxReal x mask) - k : Nat) : Real) +
        (zeroCount x : Real) := by
    exact_mod_cast hnat
  linarith

end ECRuntime
