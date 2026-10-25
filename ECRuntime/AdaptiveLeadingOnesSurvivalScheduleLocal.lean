import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
# Stage 179 pending: adaptive LeadingOnes level-survival schedule locality

Direction: Böttcher--Doerr--Neumann, fitness-dependent mutation rates.
Two admissible schedules that agree at a visited score have the same
geometric survival law while the chain remains at that score. This is a
level-local theorem; it does not assert that the global trajectory laws are
equal or that a particular score has the same entry probability.

The theorem header is approved after Round 7. The proof remains a candidate
until compiler verification and all promotion gates pass.
-/

/-- Local equality of the rate schedules suffices for equality of the
exact finite-survival probabilities at an already occupied level. -/
theorem proposed_leadingOnesAdaptive_levelSurvival_scheduleLocal
    {n : Nat} (rate rate' : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (hrate' : ∀ j : Nat, j ≤ n → 0 ≤ rate' j ∧ rate' j ≤ 1)
    (i : Fin n) (t : Nat) (x : BitString n)
    (hlevel : leadingOnes x = i.val)
    (heq : rate i.val = rate' i.val) :
    finiteLevelSurvival (leadingOnesAdaptiveTransition rate)
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) t x =
    finiteLevelSurvival (leadingOnesAdaptiveTransition rate')
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) t x := by
  rw [proposed_leadingOnesAdaptive_exactLevel_survival rate hrate i t x hlevel,
      proposed_leadingOnesAdaptive_exactLevel_survival rate' hrate' i t x hlevel,
      heq]

end ECRuntime
