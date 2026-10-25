import ECRuntime.GenericEAAnyTargetPower
import ECRuntime.ConstantExitRuntime
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P07. A runtime statement for a genuine multi-bit (1+1)-EA, obtained
using the existing exact runtime-as-survival-tsum theorem. A geometric
self-loop survival lower bound is now connected to the actual extended
expected hitting time, rather than only to a finite-horizon surrogate. -/

/-- For any objective and target, the unrestricted extended expected hitting
time dominates the contribution of indefinitely selecting empty mutation masks. -/
theorem proposed_onePlusOne_anyTarget_runtimeSup_ge_noFlipGeometric
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fitness : BitString n → Real) (target : Set (BitString n))
    (x : BitString n) (hx : x ∉ target) :
    (∑' t : Nat, ENNReal.ofReal (((1 - p) ^ n) ^ t)) ≤
      runtimeSup (onePlusOneTransition p fitness) target x := by
  classical
  rw [candidate_runtimeSup_eq_survival_tsum
    (onePlusOneTransition p fitness) target
    (onePlusOneTransition_stochastic hp0 hp1 fitness) x]
  apply ENNReal.tsum_le_tsum
  intro t
  exact ENNReal.ofReal_le_ofReal
    (proposed_onePlusOne_genericAnyTargetSurvival_ge_noFlipPower
      p hp0 hp1 fitness target x hx t)

end ECRuntime
