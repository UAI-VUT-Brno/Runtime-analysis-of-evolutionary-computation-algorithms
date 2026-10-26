import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesLocalOptimalRate
import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

namespace ECRuntime

/-!
Stage 204: new, unapproved candidate for Böttcher--Doerr--Neumann.
This compares residence within a *reached* fitness level. It does not prove
uniform level-entry probabilities or whole-run policy optimality.
-/

/-- For any admissible adaptive schedule, the locally optimal schedule
minimizes the chance of still residing at a specified initial level after
a fixed number of steps. The initial state and the compared level are fixed. -/
theorem proposed_leadingOnesAdaptive_optimalSchedule_minLevelSurvival
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (t : Nat) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    finiteLevelSurvival
        (leadingOnesAdaptiveTransition leadingOnesLocallyOptimalSchedule)
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) t x ≤
    finiteLevelSurvival (leadingOnesAdaptiveTransition rate)
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) t x := by
  have hoptRate : ∀ j : Nat, j ≤ n →
      0 ≤ leadingOnesLocallyOptimalSchedule j ∧
        leadingOnesLocallyOptimalSchedule j ≤ 1 := by
    intro j _
    obtain ⟨hjpos, hjle⟩ :=
      proposed_leadingOnesAdaptive_localSchedule_admissible j
    exact ⟨hjpos.le, hjle⟩
  let opt := leadingOnesLocallyOptimalSchedule i.val
  let p := rate i.val
  have hp : 0 ≤ p ∧ p ≤ 1 := hrate i.val (Nat.le_of_lt i.isLt)
  have ho : 0 ≤ opt ∧ opt ≤ 1 := hoptRate i.val (Nat.le_of_lt i.isLt)
  have hoptBase : 0 ≤ 1 - opt := by linarith
  have hoptPow : (1 - opt)^i.val ≤ 1 := by
    have h := pow_le_pow_left₀ hoptBase (by linarith : 1 - opt ≤ (1 : Real)) i.val
    simpa using h
  have hoptQ : opt * (1 - opt)^i.val ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hoptPow ho.1
    nlinarith
  have hnonneg : 0 ≤ 1 - opt * (1 - opt)^i.val := by linarith
  have hq : p * (1 - p)^i.val ≤ opt * (1 - opt)^i.val := by
    simpa only [opt, p, leadingOnesLocallyOptimalSchedule] using
      proposed_leadingOnesAdaptive_localExitOptimality i.val (rate i.val) hp.1 hp.2
  have hbase : 1 - opt * (1 - opt)^i.val ≤
      1 - p * (1 - p)^i.val := by linarith
  have hpow := pow_le_pow_left₀ hnonneg hbase t
  rw [proposed_leadingOnesAdaptive_exactLevel_survival
        leadingOnesLocallyOptimalSchedule hoptRate i t x hlevel,
      proposed_leadingOnesAdaptive_exactLevel_survival rate hrate i t x hlevel]
  exact hpow

end ECRuntime
