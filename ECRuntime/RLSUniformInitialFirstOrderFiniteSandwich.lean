import ECRuntime.RLSUniformInitialLogRuntimeEnvelope
import ECRuntime.RLSUniformInitialLogRuntimeLower
import Mathlib

namespace ECRuntime

/-!
Stage 151 — USER-APPROVED statement; provisional public module, full gate pending.
Source direction: Doerr--Doerr (2013), collecting coupons with a random
initial stake.  The finite-normalization statement is the immediate analytic
precursor of the headline uniform-start RLS n log n runtime law.

The approved proof compiled in Round 32 with three tactic-linter warnings;
Round 33 removes those redundant tactics and requests a clean recheck. This stage does NOT depend on the open
Stage 137 asymptotic theorem.
-/

/-- A quantitative two-sided finite-n first-order RLS estimate, uniform
in all strictly positive linear weights. Both comparison terms converge
to one because log n tends to infinity. -/
theorem proposed_rlsLinear_uniformInitial_firstOrderFiniteSandwich
    {n : Nat} (hn : 2 ≤ n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    1 - (1 : Real) / Real.log (n : Real) ≤
        ((Finset.univ.sum (fun x : BitString n =>
          (runtimeSup
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
              (by omega : 0 < n)).transition (linearFitness w))
            ({allOnes n} : Set (BitString n)) x).toReal)) /
          (2 : Real) ^ n) /
          ((n : Real) * Real.log (n : Real)) ∧
      ((Finset.univ.sum (fun x : BitString n =>
          (runtimeSup
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
              (by omega : 0 < n)).transition (linearFitness w))
            ({allOnes n} : Set (BitString n)) x).toReal)) /
          (2 : Real) ^ n) /
          ((n : Real) * Real.log (n : Real)) ≤
      1 + (1 : Real) / Real.log (n : Real) := by
  have hnpos : 0 < n := by omega
  let avg : Real :=
    (Finset.univ.sum (fun x : BitString n =>
      (runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hnpos).transition
          (linearFitness w))
        ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n
  have hupper : avg ≤ (n : Real) * (1 + Real.log (n : Real)) :=
    proposed_rlsLinear_uniformInitial_logRuntimeUpper hnpos w hw
  have hlower : (n : Real) * (Real.log ((n : Real) + 1) - 1 +
      (1 : Real) / (2 : Real) ^ n) ≤ avg :=
    proposed_rlsLinear_uniformInitial_logRuntimeLower hnpos w hw
  have hnreal : (1 : Real) < (n : Real) := by
    exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log (n : Real) := Real.log_pos hnreal
  have hnrealpos : 0 < (n : Real) := by exact_mod_cast hnpos
  have hdenpos : 0 < (n : Real) * Real.log (n : Real) :=
    mul_pos hnrealpos hlogpos
  have hlogle : Real.log (n : Real) ≤
      Real.log ((n : Real) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hpow : 0 ≤ (1 : Real) / (2 : Real) ^ n := by positivity
  have hlow : (n : Real) * (Real.log (n : Real) - 1) ≤ avg := by
    have hterm : Real.log (n : Real) - 1 ≤
        Real.log ((n : Real) + 1) - 1 + (1 : Real) / (2 : Real) ^ n := by
      linarith
    exact (mul_le_mul_of_nonneg_left hterm (le_of_lt hnrealpos)).trans hlower
  change 1 - (1 : Real) / Real.log (n : Real) ≤
      avg / ((n : Real) * Real.log (n : Real)) ∧
    avg / ((n : Real) * Real.log (n : Real)) ≤
      1 + (1 : Real) / Real.log (n : Real)
  constructor
  · apply (le_div_iff₀ hdenpos).2
    calc
      (1 - (1 : Real) / Real.log (n : Real)) *
          ((n : Real) * Real.log (n : Real)) =
        (n : Real) * (Real.log (n : Real) - 1) := by
          field_simp [ne_of_gt hlogpos]
      _ ≤ avg := hlow
  · apply (div_le_iff₀ hdenpos).2
    calc
      avg ≤ (n : Real) * (1 + Real.log (n : Real)) := hupper
      _ = (1 + (1 : Real) / Real.log (n : Real)) *
          ((n : Real) * Real.log (n : Real)) := by
          field_simp [ne_of_gt hlogpos]
          ring

end ECRuntime
