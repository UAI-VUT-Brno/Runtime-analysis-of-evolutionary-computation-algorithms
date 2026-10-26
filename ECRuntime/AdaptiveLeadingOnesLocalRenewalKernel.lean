import ECRuntime.LeadingOnesOccupationRenewal
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-! Stage 263 (P01, new proposed statement). These exact local kernel
facts are the concrete ingredients for the still-missing adaptive
first-entry / same-level occupation renewal equation. The results do
NOT assert global independence or a stopping-time theorem. -/

/-- Once the adaptive LeadingOnes process has moved above a given
level, the next transition has zero mass of returning to that level. -/
theorem proposed_leadingOnesAdaptive_aboveLevel_returnMass_zero
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (x : BitString n) (habove : i.val < leadingOnes x) :
    finiteEventMass ((leadingOnesAdaptiveTransition rate) x)
      (fun y => leadingOnes y = i.val) = 0 := by
  change finiteEventMass
    (onePlusOneTransition (rate (leadingOnes x))
      (leadingOnesReal (n := n)) x)
    (fun y => leadingOnes y = i.val) = 0
  rcases hrate (leadingOnes x) (leadingOnes_le x) with ⟨h0, h1⟩
  exact onePlusOneTransition_leadingOnes_aboveLevel_scoreMass_eq_zero
    h0 h1 i x habove

/-- Under an adaptive rate, the probability of remaining at a reached
level is the complement of its exact local exit probability. -/
theorem proposed_leadingOnesAdaptive_exactLevel_stayMass
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (x : BitString n) (hlevel : leadingOnes x = i.val) :
    finiteEventMass ((leadingOnesAdaptiveTransition rate) x)
      (fun y => leadingOnes y = i.val) =
      1 - rate i.val * (1 - rate i.val) ^ i.val := by
  rcases hrate i.val (Nat.le_of_lt i.isLt) with ⟨h0, h1⟩
  have h := onePlusOneTransition_leadingOnes_exactLevel_stayMass_eq
    h0 h1 i x hlevel
  -- Unfold the adaptive transition *in the goal* before substituting the
  -- current level; simplifying the imported fixed-rate lemma alone leaves
  -- an opaque adaptive kernel in the expected type.
  change finiteEventMass
      (onePlusOneTransition (rate (leadingOnes x))
        (leadingOnesReal (n := n)) x)
      (fun y => leadingOnes y = i.val) =
        1 - rate i.val * (1 - rate i.val) ^ i.val
  rw [hlevel]
  simpa only [leadingOnesLevelExitProbability] using h

end ECRuntime
