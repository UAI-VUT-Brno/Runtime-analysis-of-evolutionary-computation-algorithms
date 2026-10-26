import ECRuntime.LeadingOnesScaledRate
import Mathlib

namespace ECRuntime

/-!
Stage 152 — USER-APPROVED statement; provisional public module, full gate pending.
Source: Böttcher--Doerr--Neumann (2010) fixed mutation rate for LeadingOnes.
Establishing strict antitonicity of (2-c)*exp(c) on (1,infinity) is the
uniqueness prerequisite for the currently open Stage 111 global optimum.
The Round 32 compiler found one unknown topology lemma; Round 33 supplies
the localized name repair, pending recheck.
-/

/-- The stationary-rate equation's left side is strictly decreasing
beyond c=1. In particular it has at most one root inside (1,2). -/
theorem proposed_leadingOnes_stationaryFactor_strictAntiOn :
    StrictAntiOn (fun c : Real => (2 - c) * Real.exp c) (Set.Ioi 1) := by
  have hderiv (c : Real) :
      deriv (fun x : Real => (2 - x) * Real.exp x) c =
        (1 - c) * Real.exp c := by
    have hsub : HasDerivAt (fun x : Real => (2 : Real) - x) (-1) c := by
      convert (hasDerivAt_id c).const_sub (2 : Real) using 1
      all_goals rfl
    have hprod := hsub.mul (Real.hasDerivAt_exp c)
    have hprod_deriv :
        deriv (fun x : Real => (2 - x) * Real.exp x) c =
          -1 * Real.exp c + (2 - c) * Real.exp c := by
      convert hprod.deriv using 1
      all_goals rfl
    rw [hprod_deriv]
    ring
  apply strictAntiOn_of_deriv_neg (convex_Ioi (1 : Real))
  · intro c hc
    have hcont : Continuous (fun x : Real => (2 - x) * Real.exp x) := by
      fun_prop
    exact hcont.continuousWithinAt
  · intro c hc
    have hc1 : 1 < c :=
      Set.mem_Ioi.mp (interior_subset hc)
    rw [hderiv]
    exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos c)

end ECRuntime
