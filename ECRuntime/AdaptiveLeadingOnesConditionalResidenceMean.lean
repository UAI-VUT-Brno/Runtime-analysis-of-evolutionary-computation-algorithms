import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.LeadingOnesResidence
import ECRuntime.LeadingOnesResidenceMean
import ECRuntime.AdaptiveLeadingOnesResidenceGeometricSeries
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 175 pending: adaptive LeadingOnes residence at a reached level

Paper direction: Boettcher--Doerr--Neumann (2010), fitness-dependent mutation
rates. Stages 168/171 certify level survival and monotone transition support;
Stage 174 proposes the associated geometric residence series.

The result below combines the exact *state-dependent survival law* with
geometric summation. It is conditional on starting at a particular level and
does not claim that this level is reached with probability one-half. That
visitation-law claim remains a distinct, nontrivial research obligation.

The theorem header was approved in the Round-5 follow-up. A complete proof
attempt replaces the isolated admission; only the official verifier can certify it.
-/

/-- Expected number of transitions spent at LeadingOnes level `i`, counting
its initial visit, conditional on already occupying that level, is the inverse
of the corresponding one-step exit probability. This is stated as a sum of
finite-survival probabilities; no independence of suffixes is assumed. -/
theorem proposed_leadingOnesAdaptive_conditionalResidenceMean
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (x : BitString n)
    (hlevel : leadingOnes x = i.val)
    (hpos : 0 < rate i.val) (hlt : rate i.val < 1) :
    (∑' t : Nat,
        ENNReal.ofReal
          (finiteLevelSurvival (leadingOnesAdaptiveTransition rate)
            ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
            t x)) =
      ENNReal.ofReal
        ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  have hq1 : rate i.val * (1 - rate i.val) ^ i.val ≤ 1 := by
    simpa only [leadingOnesLevelExitProbability] using
      (leadingOnesLevelExitProbability_le_one hpos hlt i)
  have hstay0 : 0 ≤ 1 - rate i.val * (1 - rate i.val) ^ i.val := by
    linarith
  calc
    (∑' t : Nat,
      ENNReal.ofReal
        (finiteLevelSurvival (leadingOnesAdaptiveTransition rate)
          ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
          t x)) =
        (∑' t : Nat,
          (ENNReal.ofReal
            (1 - rate i.val * (1 - rate i.val) ^ i.val)) ^ t) := by
      apply tsum_congr
      intro t
      rw [proposed_leadingOnesAdaptive_exactLevel_survival
        rate hrate i t x hlevel]
      exact ENNReal.ofReal_pow hstay0 t
    _ = ENNReal.ofReal
          ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) :=
      proposed_leadingOnesAdaptive_levelResidenceGeometricSeries
        rate i hpos hlt

end ECRuntime
