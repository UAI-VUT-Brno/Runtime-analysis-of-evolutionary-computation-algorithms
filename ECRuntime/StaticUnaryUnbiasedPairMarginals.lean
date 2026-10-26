import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Pair marginals of static unary-unbiased mutation

This module is the next probability layer above the promoted coordinate marginal
`Pr[i flips] = χ / n`.  It introduces the mass of masks containing two specified
coordinates and proves the symmetry facts that follow purely from unary unbiasedness.

The exact normalization by `n (n-1)` is intentionally separated from this stage.  The
main remaining combinatorial step is a finite double count showing that the aggregate
mass of ordered distinct flipped pairs is the second factorial radius moment.  Keeping
that step separate makes the literature audit around conditional pair probabilities
explicit and avoids importing the incorrect mean-only conditional estimate discussed in
the project roadmap.
-/

/-- Total probability mass of mutation masks that flip two specified coordinates. -/
noncomputable def pairFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) : ℝ :=
  ∑ mask : MutationMask n,
    if i ∈ mask ∧ j ∈ mask then law.weight mask else 0

/-- Pair-flip mass is nonnegative. -/
theorem pairFlipMass_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) :
    0 ≤ law.pairFlipMass i j := by
  unfold pairFlipMass
  apply Finset.sum_nonneg
  intro mask hmask
  by_cases hi : i ∈ mask
  · by_cases hj : j ∈ mask
    · simp [hi, hj, law.weight_nonneg mask]
    · simp [hi, hj]
  · simp [hi]

/-- Pair-flip mass is symmetric in the two specified coordinates. -/
theorem pairFlipMass_comm {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) :
    law.pairFlipMass i j = law.pairFlipMass j i := by
  unfold pairFlipMass
  apply Finset.sum_congr rfl
  intro mask hmask
  simp [and_comm]

/--
For a fixed first coordinate, all distinct second coordinates have the same pair-flip
mass.  The proof transports masks by the coordinate swap `j <-> k`; the first
coordinate is fixed because it is distinct from both swapped coordinates.
-/
theorem pairFlipMass_eq_of_same_first {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) :
    law.pairFlipMass i j = law.pairFlipMass i k := by
  classical
  unfold pairFlipMass
  let e : MutationMask n ≃ MutationMask n := swapMaskEquiv j k
  refine Fintype.sum_equiv e
    (fun mask : MutationMask n =>
      if i ∈ mask ∧ j ∈ mask then law.weight mask else 0)
    (fun mask : MutationMask n =>
      if i ∈ mask ∧ k ∈ mask then law.weight mask else 0) ?_
  intro mask
  have hcard : mask.card = (e mask).card := by
    simp [e]
  have hw : law.weight mask = law.weight (e mask) :=
    law.card_invariant hcard
  have hfix : (Equiv.swap j k) i = i :=
    Equiv.swap_apply_of_ne_of_ne hij hik
  have hiMem : i ∈ e mask ↔ i ∈ mask := by
    simp [e, swapMaskEquiv, hfix]
  have hkMem : k ∈ e mask ↔ j ∈ mask := by
    simp [e]
  by_cases hi : i ∈ mask
  · have hie : i ∈ e mask := hiMem.mpr hi
    by_cases hj : j ∈ mask
    · have hke : k ∈ e mask := hkMem.mpr hj
      simp [hi, hj, hie, hke, hw]
    · have hkne : k ∉ e mask := by
        intro hk
        exact hj (hkMem.mp hk)
      simp [hi, hj, hie, hkne]
  · have hine : i ∉ e mask := by
      intro hie
      exact hi (hiMem.mp hie)
    simp [hi, hine]

/--
Every ordered pair of distinct coordinates has the same pair-flip mass.  This is a
convenient theorem-level form of the two-coordinate exchangeability supplied by static
unary unbiasedness.
-/
theorem pairFlipMass_eq_of_distinct {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b) :
    law.pairFlipMass i j = law.pairFlipMass a b := by
  by_cases hja : j = a
  · subst a
    calc
      law.pairFlipMass i j = law.pairFlipMass j i :=
        law.pairFlipMass_comm i j
      _ = law.pairFlipMass j b :=
        law.pairFlipMass_eq_of_same_first j i b (Ne.symm hij) hab
  · calc
      law.pairFlipMass i j = law.pairFlipMass j i :=
        law.pairFlipMass_comm i j
      _ = law.pairFlipMass j a :=
        law.pairFlipMass_eq_of_same_first j i a (Ne.symm hij) hja
      _ = law.pairFlipMass a j :=
        law.pairFlipMass_comm j a
      _ = law.pairFlipMass a b :=
        law.pairFlipMass_eq_of_same_first a j b (Ne.symm hja) hab

/-- Flipping both specified coordinates is a subevent of flipping the first one. -/
theorem pairFlipMass_le_coordinateFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) :
    law.pairFlipMass i j ≤ law.coordinateFlipMass i := by
  unfold pairFlipMass coordinateFlipMass
  apply Finset.sum_le_sum
  intro mask hmask
  by_cases hi : i ∈ mask
  · by_cases hj : j ∈ mask
    · simp [hi, hj]
    · simp [hi, hj, law.weight_nonneg mask]
  · simp [hi]

/-- Consequently, in positive dimension, every pair-flip event has mass at most `χ/n`. -/
theorem pairFlipMass_le_meanRadius_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) (i j : Fin n) :
    law.pairFlipMass i j ≤ law.meanRadius / (n : ℝ) := by
  calc
    law.pairFlipMass i j ≤ law.coordinateFlipMass i :=
      law.pairFlipMass_le_coordinateFlipMass i j
    _ = law.meanRadius / (n : ℝ) :=
      law.coordinateFlipMass_eq_meanRadius_div hn i

/--
The second factorial radius moment is equivalently the mask-weighted expectation of
`|mask| (|mask|-1)`.  This is the quantity that the next stage will identify with the
aggregate mass of ordered distinct flipped coordinate pairs.
-/
theorem secondFactorialRadiusMoment_eq_sum_mask_card_pred_weight {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    law.secondFactorialRadiusMoment =
      ∑ mask : MutationMask n,
        (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
  unfold secondFactorialRadiusMoment radiusMass
  calc
    (∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) *
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            law.weight mask) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mask hmask
      have hcard : mask.card = k := (Finset.mem_powersetCard.mp hmask).2
      rw [hcard]
    _ = ∑ mask : MutationMask n,
        (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask := by
      have hdecomp :=
        Finset.sum_powerset (Finset.univ : Finset (Fin n))
          (fun mask : MutationMask n =>
            (mask.card : ℝ) * ((mask.card - 1 : ℕ) : ℝ) * law.weight mask)
      simpa using hdecomp.symm

end StaticUnaryUnbiasedMutation
end ECRuntime
