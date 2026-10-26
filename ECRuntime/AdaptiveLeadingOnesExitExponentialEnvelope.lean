import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
# Stage 184 pending: exponential envelope for adaptive level-exit probability

Source direction: Böttcher--Doerr--Neumann, fitness-dependent mutation rates.
The elementary inequality 1-p <= exp(-p) bounds the exact one-level
exit probability p(1-p)^i by p exp(-i p). This supplies an analytic
upper envelope for rate optimization and asymptotic comparisons.

It says nothing about level-visitation probabilities or global policy
optimality. The theorem is a new proposal awaiting human approval.
-/

/-- An exponential majorant for the adaptive LeadingOnes exit mass.
The inequality holds also at the rate endpoints p=0 and p=1. -/
theorem proposed_leadingOnesAdaptive_localExitExponentialEnvelope
    (i : Nat) (p : Real) (hp0 : 0 <= p) (hp1 : p <= 1) :
    p * (1 - p) ^ i <= p * Real.exp (-(i : Real) * p) := by
  have hbase : 1 - p <= Real.exp (-p) := Real.one_sub_le_exp_neg p
  have hn : 0 <= 1 - p := by linarith
  have hpow : (1 - p) ^ i <= (Real.exp (-p)) ^ i :=
    pow_le_pow_left₀ hn hbase i
  calc
    p * (1 - p) ^ i <= p * (Real.exp (-p)) ^ i :=
      mul_le_mul_of_nonneg_left hpow hp0
    _ = p * Real.exp (-(i : Real) * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf

end ECRuntime
