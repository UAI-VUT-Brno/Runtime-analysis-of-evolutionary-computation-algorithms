import ECRuntime.StaticUnaryUnbiasedGlobalDrift
import ECRuntime.MultiplicativeDrift
import ECRuntime.UnrestrictedRuntime
import Mathlib

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Runtime consequences of corrected multiplicative drift

The Stage-83 global drift estimate implies a strictly positive multiplicative
rate, a named generic drift certificate, and an unrestricted hitting-time
bound for the elitist transition of any static unary-unbiased mutation law.

The coefficient still depends on the law through its one-bit mass and on the
corrected potential through the factorial-moment calibration. This is a
finite-state expected-runtime certificate, not a claim of the sharp asymptotic
bound of Doerr--Janett--Lengler (2024).

This Stage-84 module is a candidate until checked by the pinned Lean compiler.
-/

/-- The calibrated one-step drift coefficient is strictly positive for a
positive one-bit mutation mass and slack parameter strictly above one. -/
theorem correctedLinearPotential_multiplicativeRate_pos
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < (law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha) := by
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hrecip : (1 : ℝ) / alpha < 1 := by
    apply (div_lt_iff₀ halphaPos).2
    simpa using halpha
  exact mul_pos (div_pos hp1 hnreal) (sub_pos.mpr hrecip)

/-- The corrected potential satisfies the generic multiplicative-drift
predicate for the *actual* static unary-unbiased elitist transition. -/
theorem correctedLinearPotential_hasMultiplicativeDriftLowerBound
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 1 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) :
    HasMultiplicativeDriftLowerBound
      (law.transition (linearFitness w))
      (law.correctedLinearPotential alpha w)
      ((law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha)) := by
  intro x _hx
  exact law.correctedLinearPotential_global_multiplicative_drift_lower_bound
    hn hp1 halpha w hw hmono x

/-- The unrestricted expected first-hitting-time certificate for the all-ones
optimum. The logarithmic certificate uses minimum positive potential one; no
asymptotic estimate for the maximum calibrated potential is asserted. -/
theorem correctedLinearPotential_runtimeSup_le
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 1 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup (law.transition (linearFitness w))
        ({allOnes n} : Set (BitString n)) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          ((law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha)) 1
          (law.correctedLinearPotential alpha w) x) := by
  have halphaNonneg : 0 ≤ alpha :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt halpha)
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  have hdelta :
      0 < (law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha) :=
    law.correctedLinearPotential_multiplicativeRate_pos hn hp1 halpha
  have hV : ∀ z : BitString n,
      0 ≤ law.correctedLinearPotential alpha w z := by
    intro z
    exact law.correctedLinearPotential_nonneg halphaNonneg w hw hmono z
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget (law.correctedLinearPotential alpha w) →
        (1 : ℝ) ≤ law.correctedLinearPotential alpha w z := by
    intro z hz
    have hnot : z ≠ allOnes n := by
      intro heq
      apply hz
      change law.correctedLinearPotential alpha w z = 0
      exact (law.correctedLinearPotential_eq_zero_iff
        halphaNonneg w hw hmono z).2 heq
    have hzero : zeroCount z ≠ 0 := by
      intro heq
      exact hnot ((zeroCount_eq_zero_iff_allOnes z).mp heq)
    have hone : 1 ≤ zeroCount z := Nat.one_le_iff_ne_zero.mpr hzero
    have honeReal : (1 : ℝ) ≤ (zeroCount z : ℝ) := by
      exact_mod_cast hone
    exact honeReal.trans
      (law.zeroCount_le_correctedLinearPotential halphaNonneg w hw hmono z)
  have hmult : HasMultiplicativeDriftLowerBound
      (law.transition (linearFitness w))
      (law.correctedLinearPotential alpha w)
      ((law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha)) :=
    law.correctedLinearPotential_hasMultiplicativeDriftLowerBound
      hn hp1 halpha w hw hmono
  have hbound := multiplicativeDrift_runtimeSup_le
    (law.transition (linearFitness w))
    (law.correctedLinearPotential alpha w)
    ((law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha)) 1
    hP hdelta (by norm_num) hV hmin hmult x
  have htarget :
      realPotentialTarget (law.correctedLinearPotential alpha w) =
        ({allOnes n} : Set (BitString n)) := by
    ext z
    change law.correctedLinearPotential alpha w z = 0 ↔ z = allOnes n
    exact law.correctedLinearPotential_eq_zero_iff
      halphaNonneg w hw hmono z
  calc
    runtimeSup (law.transition (linearFitness w))
        ({allOnes n} : Set (BitString n)) x =
      runtimeSup (law.transition (linearFitness w))
        (realPotentialTarget (law.correctedLinearPotential alpha w)) x := by
          symm
          exact runtimeSup_congr_target
            (law.transition (linearFitness w))
            (realPotentialTarget (law.correctedLinearPotential alpha w))
            ({allOnes n} : Set (BitString n)) htarget x
    _ ≤ ENNReal.ofReal
        (multiplicativeDriftRuntime
          ((law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha)) 1
          (law.correctedLinearPotential alpha w) x) := hbound

end StaticUnaryUnbiasedMutation
end ECRuntime
