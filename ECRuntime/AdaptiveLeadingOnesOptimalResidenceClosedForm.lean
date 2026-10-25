import ECRuntime.AdaptiveLeadingOnesOptimalExitClosedForm
import Mathlib

namespace ECRuntime

/-!
Stage 200 (human-approved in proof-16 follow-up): algebraic closed form of the *conditional*
residence cost under the locally optimal schedule. This follows directly
from Stage 198 and does NOT assert global adaptive policy optimality.
-/

/-- The reciprocal optimal exit mass has the exact closed form
`(i+1)^(i+1)/i^i`, including the zero-level convention. -/
theorem proposed_leadingOnesAdaptive_optimalResidence_closedForm (i : Nat) :
    (leadingOnesLocallyOptimalSchedule i *
        (1 - leadingOnesLocallyOptimalSchedule i)^i)⁻¹ =
      (((i+1 : Nat) : Real)^(i+1)) / ((i : Real)^i) := by
  rw [proposed_leadingOnesAdaptive_optimalExitMass_closedForm]
  rw [inv_div]

end ECRuntime
