import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.LeadingOnesOccupationTotalClosure
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 174 pending: adaptive LeadingOnes expected residence bridge

Source direction: Böttcher--Doerr--Neumann (2010), fitness-dependent mutation
rates. Stages 168 and 171 certify the adaptive Markov kernel, its constant
one-level exit probability, the geometric survival law and monotone support.

The present statement identifies the summed geometric stay probabilities at
a level whose mutation rate is chosen by the schedule. By design it depends
only on the rate at that *particular* level: it makes no claim that the
sequence of visited scores has the same law as under a fixed rate. The
uniform-initialization visit-mass theorem and optimization of the adaptive
policy are still separate tasks.

The user approved the statement in Round 5. An admission-free Lean proof and
all official promotion gates are still required before public integration.
-/

/-- The sum of the adaptive exact-level stay factors is the reciprocal exit
probability whenever the rate at that level belongs to `(0,1)`. This is the
geometric-residence component of the adaptive fitness-level runtime proof. -/
theorem proposed_leadingOnesAdaptive_levelResidenceGeometricSeries
    {n : ℕ} (rate : ℕ → ℝ) (i : Fin n)
    (hpos : 0 < rate i.val) (hlt : rate i.val < 1) :
    (∑' t : ℕ,
      (ENNReal.ofReal
        (1 - rate i.val * (1 - rate i.val) ^ i.val)) ^ t) =
      ENNReal.ofReal
        ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  simpa only [leadingOnesLevelStayENNReal,
    leadingOnesLevelExitProbability,
    leadingOnesVisitedLevelMeanResidence] using
    (tsum_leadingOnesLevelStayENNReal_pow_eq_ofReal_meanResidence
      (p := rate i.val) hpos hlt i)

end ECRuntime
