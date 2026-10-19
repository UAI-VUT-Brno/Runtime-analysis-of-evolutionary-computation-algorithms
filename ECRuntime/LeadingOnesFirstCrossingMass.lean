import ECRuntime.LeadingOnesFirstCrossingSymmetry
import Mathlib

namespace ECRuntime

/-!
# Stage 27 fix 5: finite first-crossing mass equality for LeadingOnes

Stage 27 fix 4 fix 1 compiler-verifies a weight-preserving involution on finite
LeadingOnes histories: toggling coordinate `i` in the complete history preserves every
pre-crossing trajectory weight and exchanges terminal first crossing at exact level `i`
with strict skipping above `i`.

This file performs the finite summation step.  The history flip is packaged as an
explicit equivalence of the finite history space.  Re-indexing the exact-entry sum by
that equivalence, and using the verified predicate exchange and weight preservation,
shows that exact-entry and strict-skip masses are equal at every finite crossing time.
Consequently each branch is one half of the total finite first-crossing mass.

No infinite-horizon normalization is claimed here.  The next slice can sum these
finite-time identities across crossing times and establish eventual crossing, yielding
the classical `1/2` probability of visiting every nonterminal LeadingOnes level under
uniform initialization.
-/

/-- The whole-history coordinate flip, packaged as a self-equivalence of the finite
history space. -/
def leadingOnesFiniteHistoryFlipEquiv {n t : ℕ} (i : Fin n) :
    LeadingOnesFiniteHistory n t ≃ LeadingOnesFiniteHistory n t where
  toFun := leadingOnesFiniteHistoryFlip i
  invFun := leadingOnesFiniteHistoryFlip i
  left_inv := by
    intro h
    exact leadingOnesFiniteHistoryFlip_involutive i h
  right_inv := by
    intro h
    exact leadingOnesFiniteHistoryFlip_involutive i h

@[simp] theorem leadingOnesFiniteHistoryFlipEquiv_apply
    {n t : ℕ} (i : Fin n) (h : LeadingOnesFiniteHistory n t) :
    leadingOnesFiniteHistoryFlipEquiv i h = leadingOnesFiniteHistoryFlip i h := by
  rfl

/-- Uniform-initialization mass of finite histories whose first crossing of boundary
`i` lands exactly at level `i`. -/
noncomputable def leadingOnesFirstCrossingExactMass
    {n t : ℕ} (p : ℝ) (i : Fin n) : ℝ := by
  classical
  exact ∑ h : LeadingOnesFiniteHistory n t,
    if leadingOnesFirstCrossingExact i h then
      leadingOnesUniformFiniteHistoryWeight p h
    else 0

/-- Uniform-initialization mass of finite histories whose first crossing of boundary
`i` skips strictly above level `i`. -/
noncomputable def leadingOnesFirstCrossingSkipMass
    {n t : ℕ} (p : ℝ) (i : Fin n) : ℝ := by
  classical
  exact ∑ h : LeadingOnesFiniteHistory n t,
    if leadingOnesFirstCrossingSkip i h then
      leadingOnesUniformFiniteHistoryWeight p h
    else 0

/-- At every fixed finite crossing time, exact entry and strict skip have equal mass.

The proof is a direct re-indexing of the exact-entry sum by the verified whole-history
coordinate-flip equivalence. -/
theorem leadingOnesFirstCrossingExactMass_eq_skipMass
    {n t : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesFirstCrossingExactMass (t := t) p i =
      leadingOnesFirstCrossingSkipMass (t := t) p i := by
  classical
  unfold leadingOnesFirstCrossingExactMass leadingOnesFirstCrossingSkipMass
  refine Fintype.sum_equiv (leadingOnesFiniteHistoryFlipEquiv (t := t) i)
    (fun h : LeadingOnesFiniteHistory n t =>
      if leadingOnesFirstCrossingExact i h then
        leadingOnesUniformFiniteHistoryWeight p h
      else 0)
    (fun h : LeadingOnesFiniteHistory n t =>
      if leadingOnesFirstCrossingSkip i h then
        leadingOnesUniformFiniteHistoryWeight p h
      else 0) ?_
  intro h
  change
    (if leadingOnesFirstCrossingExact i h then
        leadingOnesUniformFiniteHistoryWeight p h
      else 0) =
      (if leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h) then
        leadingOnesUniformFiniteHistoryWeight p (leadingOnesFiniteHistoryFlip i h)
      else 0)
  by_cases hexact : leadingOnesFirstCrossingExact i h
  · have hskipFlip :
        leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h) :=
      (leadingOnesFirstCrossingSkip_flip_iff_exact i h).2 hexact
    have hpre : leadingOnesHistoryPreCrossing i h := hexact.1
    rw [if_pos hexact, if_pos hskipFlip]
    exact (leadingOnesUniformFiniteHistoryWeight_flip p i h hpre).symm
  · have hnotSkipFlip :
        ¬ leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h) := by
      intro hskipFlip
      exact hexact ((leadingOnesFirstCrossingSkip_flip_iff_exact i h).1 hskipFlip)
    rw [if_neg hexact, if_neg hnotSkipFlip]

/-- Total finite first-crossing mass at boundary `i` and time `t`. -/
noncomputable def leadingOnesFirstCrossingMass
    {n t : ℕ} (p : ℝ) (i : Fin n) : ℝ :=
  leadingOnesFirstCrossingExactMass (t := t) p i +
    leadingOnesFirstCrossingSkipMass (t := t) p i

/-- The total finite first-crossing mass is twice the exact-entry mass. -/
theorem leadingOnesFirstCrossingMass_eq_two_mul_exactMass
    {n t : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesFirstCrossingMass (t := t) p i =
      2 * leadingOnesFirstCrossingExactMass (t := t) p i := by
  unfold leadingOnesFirstCrossingMass
  rw [← leadingOnesFirstCrossingExactMass_eq_skipMass (t := t) p i]
  ring

/-- Equivalently, exact entry accounts for one half of the finite first-crossing mass. -/
theorem leadingOnesFirstCrossingExactMass_eq_half_crossingMass
    {n t : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesFirstCrossingExactMass (t := t) p i =
      (1 / 2 : ℝ) * leadingOnesFirstCrossingMass (t := t) p i := by
  rw [leadingOnesFirstCrossingMass_eq_two_mul_exactMass (t := t) p i]
  ring

/-- The strict-skip branch has the same one-half representation. -/
theorem leadingOnesFirstCrossingSkipMass_eq_half_crossingMass
    {n t : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesFirstCrossingSkipMass (t := t) p i =
      (1 / 2 : ℝ) * leadingOnesFirstCrossingMass (t := t) p i := by
  rw [← leadingOnesFirstCrossingExactMass_eq_skipMass (t := t) p i]
  exact leadingOnesFirstCrossingExactMass_eq_half_crossingMass (t := t) p i

end ECRuntime
