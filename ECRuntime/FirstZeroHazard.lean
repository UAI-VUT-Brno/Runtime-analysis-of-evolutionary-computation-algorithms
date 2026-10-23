import ECRuntime.StaticUnaryUnbiasedLowestMaskBinVal
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LeadingOnesResidence
import ECRuntime.LeadingOnesBoundaryEventualCrossing
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
Stage 112 (A4) promotion-preparation source: closed first-zero mutation hazard by radius mixture.
The Stage-99 denominator-free `lowestMaskEvent_radius_choose_mass` is the
main ingredient. No runtime equality is implied by the hazard identity alone.
-/

/-- The minimum-flipped-index hazard is the binomial mixture over positive
radii; the denominator is nonzero for all k in Icc 1 n. -/
theorem lowestMaskEvent_mass_eq_radius_mixture
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (i : Fin n) :
    law.maskEventMass (lowestMaskEvent i) =
      Finset.sum (Finset.Icc 1 n)
        (fun k =>
          ((Nat.choose (n - 1 - i.val) (k - 1) : Real) /
            (Nat.choose n k : Real)) * law.radiusMass k) := by
  classical
  let s := lowestMaskEvent i
  have hdecomp :
      (∑ k ∈ Finset.range (n + 1),
        law.maskEventMass (s.filter (fun mask => mask.card = k))) =
        law.maskEventMass s := by
    unfold maskEventMass
    calc
      (∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ s.filter (fun mask => mask.card = k), law.weight mask) =
          ∑ k ∈ Finset.range (n + 1),
            ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
              if mask ∈ s then law.weight mask else 0 := by
                apply Finset.sum_congr rfl
                intro k _
                calc
                  (∑ mask ∈ s.filter (fun mask => mask.card = k), law.weight mask) =
                    ∑ mask : MutationMask n,
                      if mask ∈ s.filter (fun mask => mask.card = k) then
                        law.weight mask else 0 :=
                          (Finset.sum_ite_mem_eq _ _).symm
                  _ = ∑ mask : MutationMask n,
                        if mask ∈ Finset.powersetCard k
                          (Finset.univ : Finset (Fin n)) then
                            (if mask ∈ s then law.weight mask else 0) else 0 := by
                      apply Finset.sum_congr rfl
                      intro mask _
                      simp only [Finset.mem_filter, Finset.mem_powersetCard]
                      simp only [Finset.subset_univ, true_and]
                      by_cases hm : mask ∈ s <;>
                        by_cases hk : mask.card = k <;> simp [hm, hk]
                  _ = ∑ mask ∈ Finset.powersetCard k
                        (Finset.univ : Finset (Fin n)),
                        if mask ∈ s then law.weight mask else 0 :=
                          Finset.sum_ite_mem_eq _ _
      _ = ∑ mask : MutationMask n, if mask ∈ s then law.weight mask else 0 := by
        -- `sum_powerset` sums over `range (univ.card + 1)` and over the
        -- powerset of `univ`.  Both indexing sets are definitionally finite,
        -- but not definitionally the same as our explicit `n+1` and `univ`.
        have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
        have hpowerset :
            (Finset.univ : Finset (Fin n)).powerset =
              (Finset.univ : Finset (MutationMask n)) := by
          ext mask
          simp
        simpa only [hcard, hpowerset] using
          ((Finset.sum_powerset (Finset.univ : Finset (Fin n))
            (fun mask => if mask ∈ s then law.weight mask else 0)).symm)
      _ = ∑ mask ∈ s, law.weight mask := by
        exact Finset.sum_ite_mem_eq s law.weight
  have hzero : law.maskEventMass (s.filter (fun mask => mask.card = 0)) = 0 := by
    unfold maskEventMass
    apply Finset.sum_eq_zero
    intro mask hm
    have hms : mask ∈ lowestMaskEvent i := (Finset.mem_filter.mp hm).1
    have hc : mask.card = 0 := (Finset.mem_filter.mp hm).2
    have him : i ∈ mask := lowestMaskEvent_supports_pivot i mask hms
    have : 0 < mask.card := Finset.card_pos.mpr ⟨i, him⟩
    omega
  have hset : (Finset.range (n + 1)).erase 0 = Finset.Icc 1 n := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hpart :
      law.maskEventMass s =
        ∑ k ∈ Finset.Icc 1 n,
          law.maskEventMass (s.filter (fun mask => mask.card = k)) := by
    have hz : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsum := Finset.sum_erase_add (Finset.range (n + 1))
      (fun k => law.maskEventMass (s.filter (fun mask => mask.card = k))) hz
    rw [hset, hzero, add_zero] at hsum
    exact hdecomp.symm.trans hsum.symm
  rw [hpart]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hchooseNat : 0 < Nat.choose n k := Nat.choose_pos hkn
  have hchoose : (Nat.choose n k : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hchooseNat)
  have hcount := law.lowestMaskEvent_radius_choose_mass i k hk1 hkn
  have hratio : law.maskEventMass (s.filter (fun mask => mask.card = k)) =
      ((Nat.choose (n - 1 - i.val) (k - 1) : Real) * law.radiusMass k) /
        (Nat.choose n k : Real) := by
    apply (eq_div_iff hchoose).2
    simpa [s, mul_comm] using hcount
  calc
    law.maskEventMass (s.filter (fun mask => mask.card = k)) =
        ((Nat.choose (n - 1 - i.val) (k - 1) : Real) * law.radiusMass k) /
          (Nat.choose n k : Real) := hratio
    _ = ((Nat.choose (n - 1 - i.val) (k - 1) : Real) /
          (Nat.choose n k : Real)) * law.radiusMass k := by ring

/-- For uniform one-bit mutation, every minimum-flipped-index hazard is 1/n. -/
theorem uniformOneBitLaw_lowestMaskEvent_mass
    {n : Nat} (hn : 0 < n) (i : Fin n) :
    (uniformOneBitLaw hn).maskEventMass (lowestMaskEvent i) =
      1 / (n : Real) := by
  rw [lowestMaskEvent_mass_eq_radius_mixture]
  simp_rw [uniformOneBitLaw_radiusMass hn]
  simp only [mul_ite, mul_one, mul_zero]
  have hm : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_refl _, hn⟩
  rw [Finset.sum_ite_eq']
  simp [hm]

/-- For independent bit mutation, the minimum-flipped-index hazard is
p*(1-p)^i (the event flips i and no more important coordinate). -/
theorem independentBitLaw_lowestMaskEvent_mass
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    (independentBitLaw (n := n) p hp0 hp1).maskEventMass
      (lowestMaskEvent i) = p * (1 - p) ^ i.val := by
  classical
  have hfamily : lowestMaskEvent i = leadingOnesExitMaskFamily i := by
    ext mask
    rw [mem_lowestMaskEvent_iff,
      ← leadingOnesExitMaskEvent_iff_mem_family]
    constructor
    · rintro ⟨hi, hmin⟩
      refine ⟨hi, ?_⟩
      intro j hj hjmem
      exact (Nat.not_le_of_gt hj) (hmin j hjmem)
    · rintro ⟨hi, hprefix⟩
      refine ⟨hi, ?_⟩
      intro j hjmem
      by_contra hnot
      have hj : j.val < i.val := Nat.lt_of_not_ge hnot
      exact hprefix j hj hjmem
  change (∑ mask ∈ lowestMaskEvent i, mutationMaskWeight p mask) =
    p * (1 - p) ^ i.val
  rw [hfamily]
  exact leadingOnesExitMaskFamily_weight_eq p i

end StaticUnaryUnbiasedMutation
end ECRuntime
