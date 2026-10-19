import ECRuntime.StaticUnaryUnbiasedPairMarginals
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Exact normalization of unary-unbiased pair marginals

Stage 71 promoted the exchangeability of all distinct coordinate-pair flip events and
identified the second factorial radius moment with the mask expectation of
`|M| (|M|-1)`.  This module closes the remaining finite double count.

For a mutation law with radius `K`, the aggregate mass of ordered distinct flipped
coordinate pairs is exactly `E[K(K-1)]`.  Since static unary unbiasedness makes all
ordered distinct coordinate pairs equiprobable, every specified pair `i != j` has mass

`E[K(K-1)] / (n (n-1))`.

Dividing by the promoted coordinate marginal `Pr[j flips] = chi / n` gives the correct
size-biased conditional ratio

`Pr[i flips and j flips] / Pr[j flips]
   = E[K(K-1)] / (chi (n-1))`

when `chi > 0`.  No bound replacing the factorial moment by `chi^2` or `chi` is assumed.
-/

/-- Aggregate probability mass of all ordered distinct coordinate-pair flip events. -/
noncomputable def orderedDistinctPairMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), law.pairFlipMass i j

/-- The aggregate ordered-distinct-pair mass is nonnegative. -/
theorem orderedDistinctPairMass_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.orderedDistinctPairMass := by
  unfold orderedDistinctPairMass
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact law.pairFlipMass_nonneg i j

/--
For a fixed mask, summing one constant over all ordered distinct pairs contained in the
mask gives `|M| (|M|-1)` copies of that constant.
-/
private theorem sum_ordered_distinct_members_eq_card_mul_pred {n : ℕ}
    (mask : MutationMask n) (w : ℝ) :
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        if i ∈ mask ∧ j ∈ mask then w else 0) =
      (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * w := by
  classical
  have hinner : ∀ i : Fin n,
      (∑ j ∈ (Finset.univ.erase i),
          if i ∈ mask ∧ j ∈ mask then w else 0) =
        if i ∈ mask then ((mask.card - 1 : ℕ) : ℝ) * w else 0 := by
    intro i
    by_cases hi : i ∈ mask
    · calc
        (∑ j ∈ (Finset.univ.erase i),
            if i ∈ mask ∧ j ∈ mask then w else 0) =
            ∑ j ∈ (Finset.univ.erase i), if j ∈ mask then w else 0 := by
              simp [hi]
        _ = ∑ j ∈ (mask.erase i), w := by
              have hfilter :
                  (Finset.univ.erase i).filter (fun j : Fin n => j ∈ mask) =
                    mask.erase i := by
                ext j
                simp [Finset.mem_erase]
              rw [← hfilter]
              exact (Finset.sum_filter (fun j : Fin n => j ∈ mask)
                (fun _j : Fin n => w)).symm
        _ = ((mask.erase i).card : ℝ) * w := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((mask.card - 1 : ℕ) : ℝ) * w := by
              rw [Finset.card_erase_of_mem hi]
        _ = if i ∈ mask then ((mask.card - 1 : ℕ) : ℝ) * w else 0 := by
              simp [hi]
    · simp [hi]
  calc
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        if i ∈ mask ∧ j ∈ mask then w else 0) =
        ∑ i : Fin n,
          if i ∈ mask then ((mask.card - 1 : ℕ) : ℝ) * w else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hinner i
    _ = ∑ i ∈ mask, ((mask.card - 1 : ℕ) : ℝ) * w := by
      exact Finset.sum_ite_mem_eq mask
        (fun _i : Fin n => ((mask.card - 1 : ℕ) : ℝ) * w)
    _ = (mask.card : ℝ) * (((mask.card - 1 : ℕ) : ℝ) * w) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * w := by
      ring

/-- Finite double count: aggregate ordered-distinct-pair mass equals `E[K(K-1)]`. -/
theorem orderedDistinctPairMass_eq_secondFactorialRadiusMoment {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    law.orderedDistinctPairMass = law.secondFactorialRadiusMoment := by
  classical
  rw [law.secondFactorialRadiusMoment_eq_sum_mask_card_pred_weight]
  unfold orderedDistinctPairMass pairFlipMass
  calc
    (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        ∑ mask : MutationMask n,
          if i ∈ mask ∧ j ∈ mask then law.weight mask else 0) =
        ∑ i : Fin n, ∑ mask : MutationMask n,
          ∑ j ∈ (Finset.univ.erase i),
            if i ∈ mask ∧ j ∈ mask then law.weight mask else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ mask : MutationMask n, ∑ i : Fin n,
          ∑ j ∈ (Finset.univ.erase i),
            if i ∈ mask ∧ j ∈ mask then law.weight mask else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ mask : MutationMask n,
        (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
      apply Finset.sum_congr rfl
      intro mask hmask
      exact sum_ordered_distinct_members_eq_card_mul_pred mask (law.weight mask)

/--
By pair exchangeability, the aggregate ordered-distinct-pair mass is `n(n-1)` times the
mass of any specified distinct pair.
-/
theorem orderedDistinctPairMass_eq_n_mul_pred_mul_pairFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) (hij : i ≠ j) :
    law.orderedDistinctPairMass =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * law.pairFlipMass i j := by
  classical
  unfold orderedDistinctPairMass
  calc
    (∑ a : Fin n, ∑ b ∈ (Finset.univ.erase a), law.pairFlipMass a b) =
        ∑ a : Fin n, ∑ _b ∈ (Finset.univ.erase a), law.pairFlipMass i j := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      exact law.pairFlipMass_eq_of_distinct a b i j (Ne.symm hba) hij
    _ = ∑ _a : Fin n,
        ((n - 1 : ℕ) : ℝ) * law.pairFlipMass i j := by
      apply Finset.sum_congr rfl
      intro a ha
      have hcard : (Finset.univ.erase a).card = n - 1 := by simp
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (n : ℝ) * (((n - 1 : ℕ) : ℝ) * law.pairFlipMass i j) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * law.pairFlipMass i j := by
      ring

/-- Exact probability mass of a specified pair of distinct flipped coordinates. -/
theorem pairFlipMass_eq_secondFactorialRadiusMoment_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (i j : Fin n) (hij : i ≠ j) :
    law.pairFlipMass i j =
      law.secondFactorialRadiusMoment /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  have hagg := law.orderedDistinctPairMass_eq_secondFactorialRadiusMoment
  have hconst := law.orderedDistinctPairMass_eq_n_mul_pred_mul_pairFlipMass i j hij
  have hmul :
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * law.pairFlipMass i j =
        law.secondFactorialRadiusMoment :=
    hconst.symm.trans hagg
  have hnpos : 0 < n := by omega
  have hpredpos : 0 < n - 1 := by omega
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hpred0 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpredpos)
  have hden0 : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≠ 0 := mul_ne_zero hn0 hpred0
  apply (eq_div_iff hden0).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/--
The correct conditional pair-flip ratio.  When `χ > 0`, conditioning on a specified
coordinate flip size-biases the radius distribution and gives the factorial-moment
ratio rather than a mean-only expression.
-/
theorem pairFlipMass_div_coordinateFlipMass_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hchi : 0 < law.meanRadius) (i j : Fin n) (hij : i ≠ j) :
    law.pairFlipMass i j / law.coordinateFlipMass j =
      law.secondFactorialRadiusMoment /
        (law.meanRadius * ((n - 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  rw [law.pairFlipMass_eq_secondFactorialRadiusMoment_div hn i j hij]
  rw [law.coordinateFlipMass_eq_meanRadius_div hnpos j]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hpredpos : 0 < n - 1 := by omega
  have hpred0 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpredpos)
  have hchi0 : law.meanRadius ≠ 0 := ne_of_gt hchi
  field_simp [hn0, hpred0, hchi0]

end StaticUnaryUnbiasedMutation
end ECRuntime
