import ECRuntime.AdaptiveLeadingOnesFiniteOccupationRenewal
import ECRuntime.AdaptiveLeadingOnesScalarRenewalSolution
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 275 (P01, dependent research proposal).
Instantiates finite scalar renewal uniqueness with the *genuine*
adaptive LeadingOnes finite-trajectory occupation masses. This theorem
requires both Stages 273 and 274 to have passed official promotion.
It does not claim the infinite-horizon occupation sum has been evaluated.
-/

/-- Actual real-weight finite-trajectory occupation mass at exact level `i`. -/
noncomputable def leadingOnesAdaptiveFiniteOccupationMass
    {n : Nat} (rate : Nat → Real) (x : BitString n) (i : Fin n)
    (t : Nat) : Real :=
  finiteTrajectorySetWeight (leadingOnesAdaptiveTransition rate) t x
    (leadingOnesFiniteScoreLevelAtHorizonSet x i t)

/-- Actual mass of new arrivals at exact level `i` from below on the
transition between times `t` and `t+1`. -/
noncomputable def leadingOnesAdaptiveFiniteNewEntryMass
    {n : Nat} (rate : Nat → Real) (x : BitString n) (i : Fin n)
    (t : Nat) : Real :=
  finiteTrajectorySetWeight (leadingOnesAdaptiveTransition rate) (t + 1) x
    (leadingOnesFiniteBelowThenExactAtNextSet x i t)

/-- The genuine adaptive finite-horizon occupation sequence is precisely
the scalar renewal solution with the local stay coefficient. -/
theorem proposed_leadingOnesAdaptive_finiteOccupation_eq_renewalSolution
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    leadingOnesAdaptiveFiniteOccupationMass rate x i t =
      finiteOccupationRenewalSolution
        (1 - rate i.val * (1 - rate i.val) ^ i.val)
        (leadingOnesAdaptiveFiniteOccupationMass rate x i 0)
        (leadingOnesAdaptiveFiniteNewEntryMass rate x i) t := by
  apply proposed_finiteOccupationRenewalSolution_unique
  intro s
  exact proposed_leadingOnesAdaptive_finiteOccupation_oneStep_renewal
    rate hrate x i s

end ECRuntime
