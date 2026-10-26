import ECRuntime.StaticUnaryUnbiasedMutation
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P07: the no-op / singleton radius support condition makes the mean
radius exactly equal to the one-bit probability mass. This removes the
extraneous equality hypothesis from the precise harmonic runtime theorem. -/

/-- A static unary-unbiased law supported at radii zero and one has mean
radius equal to its singleton mass. -/
theorem proposed_staticUnary_singletonSupport_meanRadius_eq_oneBitMass
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1) :
    law.meanRadius = law.oneBitMass := by
  have hlarge (k : Nat) (hk : 2 ≤ k) : law.radiusMass k = 0 := by
    unfold StaticUnaryUnbiasedMutation.radiusMass
    apply Finset.sum_eq_zero
    intro mask hm
    by_contra hne
    have hcard : mask.card = k := (Finset.mem_powersetCard.mp hm).2
    have hle := hsmall mask hne
    omega
  have hterm (k : Nat) :
      (k : Real) * law.radiusMass k =
        if k = 1 then law.oneBitMass else 0 := by
    by_cases hk1 : k = 1
    · subst k
      simp [StaticUnaryUnbiasedMutation.oneBitMass]
    · by_cases hk0 : k = 0
      · subst k
        simp
      · have hk2 : 2 ≤ k := by omega
        simp [hk1, hlarge k hk2]
  calc
    law.meanRadius =
        ∑ k ∈ Finset.range (n + 1),
          (if k = 1 then law.oneBitMass else 0) := by
      unfold StaticUnaryUnbiasedMutation.meanRadius
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
    _ = if 1 ∈ Finset.range (n + 1) then law.oneBitMass else 0 := by
      simp
    _ = law.oneBitMass := by
      by_cases hn : 0 < n
      · have hm : 1 ∈ Finset.range (n + 1) := by
          simp only [Finset.mem_range]
          omega
        simp [hm]
      · have hOne : law.oneBitMass = 0 := by
          change law.radiusMass 1 = 0
          exact law.radiusMass_eq_zero_of_lt (by omega)
        simp [hOne]

end ECRuntime
