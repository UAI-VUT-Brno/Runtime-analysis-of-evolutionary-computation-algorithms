import ECRuntime.StaticUnaryUnbiasedPairNormalization
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Event-mass bridge for repaired conditional flip estimates

The published static unary-unbiased linear-function proof bounds a conditional
second-coordinate flip probability inside an accepted event.  After Stage 72, the
correct pair quantity is known exactly in terms of the second factorial radius moment.
This module isolates the remaining Bayes-style bookkeeping in a form that does not yet
commit to a particular accepted/leftmost event.

For any finite mask event `A` that

* contains the singleton mask `{i}`, and
* is supported on masks that flip coordinate `i`,

the subevent in which a distinct coordinate `j` also flips has conditional mass at most

`E[K(K-1)] / (p₁ (n-1))`.

This is the corrected generic coefficient replacing the unsupported mean-only
`χ/(n-1)` step.  Later modules can instantiate `A` with the objective-specific accepted
events from the linear-function proof.
-/

/-- Probability mass of a finite event of mutation masks. -/
noncomputable def maskEventMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (event : Finset (MutationMask n)) : ℝ :=
  ∑ mask ∈ event, law.weight mask

/-- Every finite mask-event mass is nonnegative. -/
theorem maskEventMass_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (event : Finset (MutationMask n)) :
    0 ≤ law.maskEventMass event := by
  unfold maskEventMass
  apply Finset.sum_nonneg
  intro mask hmask
  exact law.weight_nonneg mask

/-- Event mass is monotone under inclusion. -/
theorem maskEventMass_mono {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    {event₁ event₂ : Finset (MutationMask n)} (hsub : event₁ ⊆ event₂) :
    law.maskEventMass event₁ ≤ law.maskEventMass event₂ := by
  unfold maskEventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro mask h₂ h₁
  exact law.weight_nonneg mask

/-- Masks that flip both specified coordinates. -/
def pairFlipEvent {n : ℕ} (i j : Fin n) : Finset (MutationMask n) :=
  Finset.univ.filter (fun mask => i ∈ mask ∧ j ∈ mask)

/-- The finite-event mass of `pairFlipEvent` is the promoted pair-flip mass. -/
theorem maskEventMass_pairFlipEvent_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (i j : Fin n) :
    law.maskEventMass (pairFlipEvent i j) = law.pairFlipMass i j := by
  unfold maskEventMass pairFlipEvent pairFlipMass
  exact Finset.sum_filter
    (fun mask : MutationMask n => i ∈ mask ∧ j ∈ mask)
    (fun mask : MutationMask n => law.weight mask)

/-- Restrict an event to outcomes that also flip coordinate `j`. -/
def secondCoordinateSlice {n : ℕ}
    (event : Finset (MutationMask n)) (j : Fin n) : Finset (MutationMask n) :=
  event.filter (fun mask => j ∈ mask)

/--
If every mask in `event` flips `i`, then the slice in which `j` also flips is a
subevent of the pair-flip event `(i,j)`.
-/
theorem secondCoordinateSlice_subset_pairFlipEvent {n : ℕ}
    (event : Finset (MutationMask n)) (i j : Fin n)
    (hi : ∀ mask ∈ event, i ∈ mask) :
    secondCoordinateSlice event j ⊆ pairFlipEvent i j := by
  intro mask hmask
  have hmem := Finset.mem_filter.mp hmask
  have himask : i ∈ mask := hi mask hmem.1
  simp [pairFlipEvent, himask, hmem.2]

/--
Under support on coordinate `i`, the mass of the `j`-slice is at most the unconditional
pair-flip mass of `i` and `j`.
-/
theorem secondCoordinateSlice_mass_le_pairFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (i j : Fin n)
    (hi : ∀ mask ∈ event, i ∈ mask) :
    law.maskEventMass (secondCoordinateSlice event j) ≤ law.pairFlipMass i j := by
  calc
    law.maskEventMass (secondCoordinateSlice event j) ≤
        law.maskEventMass (pairFlipEvent i j) :=
      law.maskEventMass_mono (secondCoordinateSlice_subset_pairFlipEvent event i j hi)
    _ = law.pairFlipMass i j := law.maskEventMass_pairFlipEvent_eq i j

/-- If an event contains `{i}`, its mass is at least the weight of that singleton. -/
theorem singletonWeight_le_maskEventMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (i : Fin n)
    (hsingleton : ({i} : MutationMask n) ∈ event) :
    law.weight ({i} : MutationMask n) ≤ law.maskEventMass event := by
  have hsub : ({({i} : MutationMask n)} : Finset (MutationMask n)) ⊆ event := by
    intro mask hmask
    have hEq : mask = ({i} : MutationMask n) := by
      simpa using hmask
    simpa [hEq] using hsingleton
  calc
    law.weight ({i} : MutationMask n) =
        law.maskEventMass ({({i} : MutationMask n)} : Finset (MutationMask n)) := by
      simp [maskEventMass]
    _ ≤ law.maskEventMass event := law.maskEventMass_mono hsub

/--
Cross-multiplied Bayes bound: the sliced event mass times the singleton mass is at most
pair mass times the original event mass.  This form needs no positivity assumption on
`p₁` and is often the most convenient algebraic interface.
-/
theorem secondCoordinateSlice_mass_mul_singletonWeight_le {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (i j : Fin n)
    (hi : ∀ mask ∈ event, i ∈ mask)
    (hsingleton : ({i} : MutationMask n) ∈ event) :
    law.maskEventMass (secondCoordinateSlice event j) *
        law.weight ({i} : MutationMask n) ≤
      law.pairFlipMass i j * law.maskEventMass event := by
  have hnum : law.maskEventMass (secondCoordinateSlice event j) ≤
      law.pairFlipMass i j :=
    law.secondCoordinateSlice_mass_le_pairFlipMass event i j hi
  have hden : law.weight ({i} : MutationMask n) ≤ law.maskEventMass event :=
    law.singletonWeight_le_maskEventMass event i hsingleton
  exact mul_le_mul hnum hden
    (law.weight_nonneg ({i} : MutationMask n))
    (law.pairFlipMass_nonneg i j)

/--
Exact ratio of a distinct pair-flip mass to the specified singleton mass.  This is the
factorial-moment coefficient that replaces the incorrect unconditional-radius average.
-/
theorem pairFlipMass_div_singletonWeight_eq_factorialCoefficient {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass) (i j : Fin n) (hij : i ≠ j) :
    law.pairFlipMass i j / law.weight ({i} : MutationMask n) =
      law.secondFactorialRadiusMoment /
        (law.oneBitMass * ((n - 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  rw [law.pairFlipMass_eq_secondFactorialRadiusMoment_div hn i j hij]
  rw [law.singletonWeight_eq_oneBitMass_div hnpos i]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hpredpos : 0 < n - 1 := by omega
  have hpred0 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpredpos)
  have hp10 : law.oneBitMass ≠ 0 := ne_of_gt hp1
  field_simp [hn0, hpred0, hp10]

/--
Correct generic conditional bound for any event containing the singleton `{i}` and
supported on masks flipping `i`.

The left side is the finite-event analogue of
`Pr[j flips | event]`.  The right side is the exact factorial-moment coefficient
`E[K(K-1)]/(p₁(n-1))`; no mean-only replacement is made.
-/
theorem secondCoordinateSlice_mass_div_eventMass_le_factorialCoefficient {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    (event : Finset (MutationMask n)) (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ mask ∈ event, i ∈ mask)
    (hsingleton : ({i} : MutationMask n) ∈ event) :
    law.maskEventMass (secondCoordinateSlice event j) / law.maskEventMass event ≤
      law.secondFactorialRadiusMoment /
        (law.oneBitMass * ((n - 1 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hsingletonPos : 0 < law.weight ({i} : MutationMask n) := by
    rw [law.singletonWeight_eq_oneBitMass_div hnpos i]
    exact div_pos hp1 (by exact_mod_cast hnpos)
  have hdenLower : law.weight ({i} : MutationMask n) ≤ law.maskEventMass event :=
    law.singletonWeight_le_maskEventMass event i hsingleton
  have hdenPos : 0 < law.maskEventMass event :=
    lt_of_lt_of_le hsingletonPos hdenLower
  have hcross := law.secondCoordinateSlice_mass_mul_singletonWeight_le
    event i j hi hsingleton
  calc
    law.maskEventMass (secondCoordinateSlice event j) / law.maskEventMass event ≤
        law.pairFlipMass i j / law.weight ({i} : MutationMask n) := by
      apply (div_le_iff₀ hdenPos).2
      calc
        law.maskEventMass (secondCoordinateSlice event j) ≤
            (law.pairFlipMass i j * law.maskEventMass event) /
              law.weight ({i} : MutationMask n) :=
          (le_div_iff₀ hsingletonPos).2 hcross
        _ = (law.pairFlipMass i j / law.weight ({i} : MutationMask n)) *
              law.maskEventMass event := by ring
    _ = law.secondFactorialRadiusMoment /
        (law.oneBitMass * ((n - 1 : ℕ) : ℝ)) :=
      law.pairFlipMass_div_singletonWeight_eq_factorialCoefficient hn hp1 i j hij

end StaticUnaryUnbiasedMutation
end ECRuntime
