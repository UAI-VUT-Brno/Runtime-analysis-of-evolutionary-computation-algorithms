import ECRuntime.LeadingOnesBoundaryEventualCrossing
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 227 (NEW, pending approval): adaptive one-step strict progress.
This concerns the original mutation-mask distribution, not a claimed
independence property of suffix bits or a global expected-runtime bound.
-/

/-- At any state below the boundary, the adaptive mutation distribution
assigns strictly positive mass to masks that decrease the boundary potential. -/
theorem proposed_leadingOnesAdaptive_boundaryMaskProgress_pos
    {n : Nat} (rate : Nat -> Real)
    (hrate : ∀ j : Nat, j <= n -> 0 < rate j ∧ rate j < 1)
    (i : Fin n) (x : BitString n)
    (hx : 0 < leadingOnesBoundaryPotential i x) :
    0 < finiteEventMass
      (fun mask : MutationMask n =>
        mutationMaskWeight (rate (leadingOnes x)) mask)
      (fun mask => leadingOnesBoundaryPotential i
        (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
          leadingOnesBoundaryPotential i x) := by
  have hbelow : leadingOnes x < i.val := by
    simpa [leadingOnesBoundaryPotential] using hx
  have hlevel : leadingOnes x <= n :=
    (Nat.le_of_lt (lt_trans hbelow i.isLt))
  have hp0 : 0 < rate (leadingOnes x) := (hrate (leadingOnes x) hlevel).1
  have hp1 : rate (leadingOnes x) < 1 := (hrate (leadingOnes x) hlevel).2
  have hq : 0 < 1 - rate (leadingOnes x) := by linarith
  have hmask := leadingOnesBoundaryPotential_progressMass_lower
    hp0.le hp1.le i x hx
  exact (mul_pos hp0 (pow_pos hq _)).trans_le hmask

end ECRuntime
