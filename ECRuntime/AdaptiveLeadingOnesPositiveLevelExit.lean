import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 223 (NEW, unapproved, independent of Stages 218--222):
strictly positive score-dependent mutation rates below one guarantee a
strictly positive one-step exit mass from every nonterminal level.
This is a local ingredient for the finite-state eventual-crossing proof;
strict positivity alone is not silently interpreted as a proof of a.s.
hitting.
-/

/-- Strictly interior scheduled rates produce positive exit probability
from every nonterminal LeadingOnes level. -/
theorem proposed_leadingOnesAdaptive_exactLevel_exitMass_pos
    {n : Nat} (rate : Nat -> Real)
    (hrate : ∀ j : Nat, j < n -> 0 < rate j ∧ rate j < 1)
    (i : Fin n) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    0 < finiteEventMass ((leadingOnesAdaptiveTransition rate) x)
      (fun y => leadingOnes y ≠ i.val) := by
  rw [proposed_leadingOnesAdaptive_exactLevel_exitMass rate i x hlevel]
  have hp := (hrate i.val i.isLt).1
  have hq : 0 < 1 - rate i.val := by
    have hp1 := (hrate i.val i.isLt).2
    linarith
  positivity

end ECRuntime
