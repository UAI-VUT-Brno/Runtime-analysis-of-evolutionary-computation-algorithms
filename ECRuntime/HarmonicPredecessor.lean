import ECRuntime.RLSOneBitExpectationSupport
import Mathlib

namespace ECRuntime

/-! Provisional public Stage 126: the exact harmonic predecessor identity,
    useful when proving the OneMax-RLS Bellman equation of Stage 122.
    The exact theorem statement is approved; proof development is authorized. -/

/-- Removing one of `k>0` zero bits reduces the harmonic potential
    by exactly `1/k`, not merely at least this much. -/
theorem proposed_harmonicReal_sub_one
    (k : Nat) (hk : 0 < k) :
    harmonicReal (k - 1) + (1 : Real) / k = harmonicReal k := by
  exact candidate_rls_harmonic_predecessor k hk

end ECRuntime
