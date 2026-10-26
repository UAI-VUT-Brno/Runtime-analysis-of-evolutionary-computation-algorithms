import ECRuntime.StaticUnaryUnbiasedRadiusTruncation
import ECRuntime.StaticUnaryUnbiasedPivotPartition
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 89: acceptance-aware mask tails and signed drift splitting

The bounded-first-moment programme requires a distinction between the probability
of a long mutation and the signed expected change caused by an *accepted* long
mutation.  This module connects the radius distribution to the actual mask law,
then decomposes the one-step potential change without dropping negative terms.

All identities hold for arbitrary static unary-unbiased mask laws.  The
accepted-event probability estimate uses only the unconditional mean radius;
it is **not** a bound on the magnitude, sign, or expectation of the accepted
high-radius potential change.  No independence of mutation coordinates and
no uniform second-factorial-moment hypothesis is used.
-/

/-- Masks whose Hamming radius is at least the cutoff `b`. -/
def highRadiusMaskEvent {n : ℕ} (b : ℕ) : Finset (MutationMask n) :=
  Finset.univ.filter (fun mask : MutationMask n => b ≤ mask.card)

/-- Masks whose Hamming radius is strictly smaller than the cutoff `b`. -/
def shortRadiusMaskEvent {n : ℕ} (b : ℕ) : Finset (MutationMask n) :=
  Finset.univ.filter (fun mask : MutationMask n => mask.card < b)

/-- High-radius masks accepted by the elitist linear-fitness selection rule.
The acceptance predicate is *inside* the finite event; it is not a
conditional mutation distribution. -/
noncomputable def acceptedHighRadiusMaskEvent {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (b : ℕ) :
    Finset (MutationMask n) := by
  classical
  exact (highRadiusMaskEvent (n := n) b).filter
    (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask))

/-- Exact bridge from the radius distribution to the original probability
weights on masks of radius at least `b`. -/
theorem maskEventMass_highRadiusMaskEvent_eq_radiusTailMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (b : ℕ) :
    law.maskEventMass (highRadiusMaskEvent (n := n) b) =
      law.radiusTailMass b := by
  classical
  have hdecomp :
      (∑ mask : MutationMask n,
        if b ≤ mask.card then law.weight mask else 0) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            if b ≤ mask.card then law.weight mask else 0 := by
    simpa using Finset.sum_powerset (Finset.univ : Finset (Fin n))
      (fun mask : MutationMask n =>
        if b ≤ mask.card then law.weight mask else 0)
  have hradius :
      (∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            if b ≤ mask.card then law.weight mask else 0) =
        law.radiusTailMass b := by
    unfold radiusTailMass
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hbk : b ≤ k
    · rw [if_pos hbk]
      unfold radiusMass
      apply Finset.sum_congr rfl
      intro mask hmask
      have hcard : mask.card = k := (Finset.mem_powersetCard.mp hmask).2
      simp only [hcard, if_pos hbk]
    · rw [if_neg hbk]
      apply Finset.sum_eq_zero
      intro mask hmask
      have hcard : mask.card = k := (Finset.mem_powersetCard.mp hmask).2
      simp only [hcard, if_neg hbk]
  calc
    law.maskEventMass (highRadiusMaskEvent (n := n) b) =
        ∑ mask : MutationMask n,
          if b ≤ mask.card then law.weight mask else 0 := by
            unfold maskEventMass highRadiusMaskEvent
            rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range (n + 1),
          ∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            if b ≤ mask.card then law.weight mask else 0 := hdecomp
    _ = law.radiusTailMass b := hradius

/-- Accepted long-radius masks form a subset of *all* long-radius masks. -/
theorem acceptedHighRadiusMaskEvent_subset_highRadiusMaskEvent {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (b : ℕ) :
    acceptedHighRadiusMaskEvent w x b ⊆
      highRadiusMaskEvent (n := n) b := by
  classical
  intro mask hmask
  exact (Finset.mem_filter.mp hmask).1

/-- The probability of an accepted mask of radius at least `b` is at most
`χ / b`.  Importantly, this does not bound the expected *loss* on the event. -/
theorem acceptedHighRadiusMaskEvent_mass_le_meanRadius_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → ℝ) (x : BitString n) {b : ℕ} (hb : 0 < b) :
    law.maskEventMass (acceptedHighRadiusMaskEvent w x b) ≤
      law.meanRadius / (b : ℝ) := by
  calc
    law.maskEventMass (acceptedHighRadiusMaskEvent w x b) ≤
        law.maskEventMass (highRadiusMaskEvent (n := n) b) :=
      law.maskEventMass_mono
        (acceptedHighRadiusMaskEvent_subset_highRadiusMaskEvent w x b)
    _ = law.radiusTailMass b :=
      law.maskEventMass_highRadiusMaskEvent_eq_radiusTailMass b
    _ ≤ law.meanRadius / (b : ℝ) :=
      law.radiusTailMass_le_meanRadius_div hb

/-- Every finite mask sum splits into signed short- and long-radius terms.
The summand `F` may have either sign. -/
theorem sum_mask_eq_shortRadius_add_highRadius {n : ℕ}
    (b : ℕ) (F : MutationMask n → ℝ) :
    (∑ mask : MutationMask n, F mask) =
      (∑ mask ∈ shortRadiusMaskEvent (n := n) b, F mask) +
        (∑ mask ∈ highRadiusMaskEvent (n := n) b, F mask) := by
  classical
  have hpoint (mask : MutationMask n) :
      F mask =
        (if mask.card < b then F mask else 0) +
        (if b ≤ mask.card then F mask else 0) := by
    by_cases hshort : mask.card < b
    · have hlong : ¬ b ≤ mask.card := by omega
      simp [hshort, hlong]
    · have hlong : b ≤ mask.card := by omega
      simp [hshort, hlong]
  calc
    (∑ mask : MutationMask n, F mask) =
        ∑ mask : MutationMask n,
          ((if mask.card < b then F mask else 0) +
            (if b ≤ mask.card then F mask else 0)) := by
              apply Finset.sum_congr rfl
              intro mask hmask
              exact hpoint mask
    _ = (∑ mask : MutationMask n,
            if mask.card < b then F mask else 0) +
          (∑ mask : MutationMask n,
            if b ≤ mask.card then F mask else 0) := by
              rw [Finset.sum_add_distrib]
    _ = (∑ mask ∈ shortRadiusMaskEvent (n := n) b, F mask) +
          (∑ mask ∈ highRadiusMaskEvent (n := n) b, F mask) := by
            simp only [shortRadiusMaskEvent, highRadiusMaskEvent,
              Finset.sum_filter]

/-- Exact signed decomposition of the *unrestricted* one-step selected
potential change, with no monotonicity or nonnegativity requirement on `g`.
In particular, the long-radius term must not be discarded in a drift bound. -/
theorem acceptedEventWeightedPotentialDrop_univ_eq_shortRadius_add_highRadius
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ) :
    law.acceptedEventWeightedPotentialDrop Finset.univ w g x =
      law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x +
      law.acceptedEventWeightedPotentialDrop
        (highRadiusMaskEvent (n := n) b) w g x := by
  classical
  unfold acceptedEventWeightedPotentialDrop
  exact sum_mask_eq_shortRadius_add_highRadius b
    (fun mask => law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g
          (selectedAfterMask (linearFitness w) x mask)))

/-- Rejected long-radius mutations have exactly zero selected potential
change.  Therefore the signed high-radius contribution is supported on the
accepted high-radius event, *without* taking absolute values or asserting a
nonnegative contribution. -/
theorem acceptedEventWeightedPotentialDrop_highRadius_eq_acceptedHighRadius
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (b : ℕ) :
    law.acceptedEventWeightedPotentialDrop
        (highRadiusMaskEvent (n := n) b) w g x =
      law.acceptedEventWeightedPotentialDrop
        (acceptedHighRadiusMaskEvent w x b) w g x := by
  classical
  unfold acceptedEventWeightedPotentialDrop
  change (∑ mask ∈ highRadiusMaskEvent (n := n) b,
      law.weight mask *
        (linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask))) =
    ∑ mask ∈ (highRadiusMaskEvent (n := n) b).filter
        (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask)),
      law.weight mask *
        (linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask))
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp only [if_pos hacc]
  · have hdrop :
        linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask) = 0 :=
      linearErrorPotential_selected_drop_of_rejects w g x mask hacc
    simp only [if_neg hacc, hdrop, mul_zero]

end StaticUnaryUnbiasedMutation
end ECRuntime
