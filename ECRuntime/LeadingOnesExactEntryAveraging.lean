import ECRuntime.LeadingOnesLevelChargeExpectation
import ECRuntime.LeadingOnesVisitProbability
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 18: fixed-initial exact-entry slices and uniform averaging

The Stage 27 fix 17 compiler run succeeds for both the focused module and the complete
root build, but emits one `unnecessarySimpa` linter warning.  The maintained project
requires warning-free promotion, so fix 18 first replaces that one proof line by the
corresponding direct `exact` proof.

The remaining exact-runtime bridge is now local to one LeadingOnes score level.  Before
attaching the geometric post-entry survival law, it is useful to expose the exact-entry
mass in the same fixed-initial form used by the genuine trajectory expectation.  The
older visit-probability development already has the *uniform* exact-entry mass
`leadingOnesFirstCrossingExactMass`; this module refines it into fixed-initial,
exact-time slices and proves that uniform averaging and the countable time sum recover
the promoted aggregate visit mass.

No independence statement is introduced.  This is the first-entry bookkeeping half of
the final per-level factorization: a subsequent slice may fix `(x,t)`, attach the exact
post-entry survival tail to the corresponding exact-entry histories, then sum over `t`
and `x` using the identities proved here.
-/

/-- Fixed-initial mass of finite histories whose first crossing of boundary `i` occurs
at time `t` and lands exactly on score level `i`. -/
noncomputable def leadingOnesFixedInitialFirstCrossingExactMass
    {n t : ℕ} (p : ℝ) (i : Fin n) (x : BitString n) : ℝ := by
  classical
  exact ∑ path : FiniteTrajectory (BitString n) t,
    if leadingOnesFirstCrossingExact i (x, path) then
      finiteTrajectoryWeight
        (onePlusOneTransition p (leadingOnesReal (n := n))) t x path
    else 0

/-- Every fixed-initial exact-entry slice has nonnegative mass for a stochastic
mutation parameter. -/
theorem leadingOnesFixedInitialFirstCrossingExactMass_nonneg
    {n t : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) :
    0 ≤ leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  unfold leadingOnesFixedInitialFirstCrossingExactMass
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hexact : leadingOnesFirstCrossingExact i (x, path)
  · simp only [hexact, if_true]
    exact finiteTrajectoryWeight_nonneg P hP t x path
  · simp [hexact]

/-- At one exact entry time, the uniform exact-entry mass is the finite uniform average
of the corresponding fixed-initial exact-entry masses. -/
theorem leadingOnesFirstCrossingExactMass_eq_uniform_average_fixedInitialExact
    {n t : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesFirstCrossingExactMass (t := t) p i =
      ((Fintype.card (BitString n) : ℝ)⁻¹) *
        ∑ x : BitString n,
          leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x := by
  classical
  unfold leadingOnesFirstCrossingExactMass
  calc
    (∑ h : LeadingOnesFiniteHistory n t,
        if leadingOnesFirstCrossingExact i h then
          leadingOnesUniformFiniteHistoryWeight p h
        else 0) =
        ∑ x : BitString n,
          ∑ path : FiniteTrajectory (BitString n) t,
            if leadingOnesFirstCrossingExact i (x, path) then
              leadingOnesUniformFiniteHistoryWeight p (x, path)
            else 0 := by
      exact Fintype.sum_prod_type
        (fun h : BitString n × FiniteTrajectory (BitString n) t =>
          if leadingOnesFirstCrossingExact i h then
            leadingOnesUniformFiniteHistoryWeight p h
          else 0)
    _ = ∑ x : BitString n,
          ((Fintype.card (BitString n) : ℝ)⁻¹) *
            ∑ path : FiniteTrajectory (BitString n) t,
              if leadingOnesFirstCrossingExact i (x, path) then
                finiteTrajectoryWeight
                  (onePlusOneTransition p (leadingOnesReal (n := n))) t x path
              else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hexact : leadingOnesFirstCrossingExact i (x, path)
      · simp [hexact, leadingOnesUniformFiniteHistoryWeight]
      · simp [hexact]
    _ = ((Fintype.card (BitString n) : ℝ)⁻¹) *
          ∑ x : BitString n,
            leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rfl

/-- `ENNReal` form of the fixed-time exact-entry averaging identity. -/
theorem ofReal_leadingOnesFirstCrossingExactMass_eq_uniform_average_fixedInitialExact
    {n t : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          ENNReal.ofReal
            (leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x) := by
  classical
  rw [leadingOnesFirstCrossingExactMass_eq_uniform_average_fixedInitialExact p i]
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  have hcardNat : 0 < Fintype.card (BitString n) := Fintype.card_pos
  have hcardReal : 0 < (Fintype.card (BitString n) : ℝ) := by
    exact_mod_cast hcardNat
  have hfixed :
      ∀ x ∈ (Finset.univ : Finset (BitString n)),
        0 ≤ leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x := by
    intro x _hx
    exact leadingOnesFixedInitialFirstCrossingExactMass_nonneg hp0 hp1 i x
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcardReal.le)]
  rw [ENNReal.ofReal_inv_of_pos hcardReal]
  rw [ENNReal.ofReal_sum_of_nonneg hfixed]
  simp

/-- Countable exact-entry mass from one fixed initial state.  This is the scalar first-
entry object to which the post-entry residence tail will be attached next. -/
noncomputable def leadingOnesFixedInitialEventualExactEntryMass
    {n : ℕ} (p : ℝ) (i : Fin n) (x : BitString n) : ENNReal :=
  ∑' t : ℕ,
    ENNReal.ofReal
      (leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x)

/-- The promoted aggregate exact-entry mass is exactly the uniform average of the
fixed-initial countable exact-entry masses. -/
theorem leadingOnesEventualFirstCrossingExactMass_eq_uniform_average_fixedInitialExact
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    leadingOnesEventualFirstCrossingExactMass p i =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          leadingOnesFixedInitialEventualExactEntryMass p i x := by
  classical
  unfold leadingOnesEventualFirstCrossingExactMass
  unfold leadingOnesFixedInitialEventualExactEntryMass
  calc
    (∑' t : ℕ,
        ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i)) =
        ∑' t : ℕ,
          ((Fintype.card (BitString n) : ENNReal)⁻¹) *
            ∑ x : BitString n,
              ENNReal.ofReal
                (leadingOnesFixedInitialFirstCrossingExactMass
                  (t := t) p i x) := by
      apply tsum_congr
      intro t
      exact
        ofReal_leadingOnesFirstCrossingExactMass_eq_uniform_average_fixedInitialExact
          hp0 hp1 i
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑' t : ℕ,
          ∑ x : BitString n,
            ENNReal.ofReal
              (leadingOnesFixedInitialFirstCrossingExactMass
                (t := t) p i x)) := by
      exact ENNReal.tsum_mul_left
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          ∑' t : ℕ,
            ENNReal.ofReal
              (leadingOnesFixedInitialFirstCrossingExactMass
                (t := t) p i x)) := by
      congr 1
      calc
        (∑' t : ℕ,
            ∑ x : BitString n,
              ENNReal.ofReal
                (leadingOnesFixedInitialFirstCrossingExactMass
                  (t := t) p i x)) =
            ∑' t : ℕ,
              ∑' x : BitString n,
                ENNReal.ofReal
                  (leadingOnesFixedInitialFirstCrossingExactMass
                    (t := t) p i x) := by
          apply tsum_congr
          intro t
          rw [tsum_fintype]
        _ = ∑' x : BitString n,
              ∑' t : ℕ,
                ENNReal.ofReal
                  (leadingOnesFixedInitialFirstCrossingExactMass
                    (t := t) p i x) := by
          exact ENNReal.tsum_comm
        _ = ∑ x : BitString n,
              ∑' t : ℕ,
                ENNReal.ofReal
                  (leadingOnesFixedInitialFirstCrossingExactMass
                    (t := t) p i x) := by
          rw [tsum_fintype]

/-- The canonical uniform visit mass is therefore available directly as a finite
uniform average of fixed-initial exact-entry masses. -/
theorem leadingOnesUniformLevelVisitMass_eq_uniform_average_fixedInitialExact
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    leadingOnesUniformLevelVisitMass p i =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          leadingOnesFixedInitialEventualExactEntryMass p i x := by
  unfold leadingOnesUniformLevelVisitMass
  exact leadingOnesEventualFirstCrossingExactMass_eq_uniform_average_fixedInitialExact
    hp0 hp1 i

/-- In the nondegenerate mutation regime, that fixed-initial exact-entry average is
exactly one half. -/
theorem uniform_average_leadingOnesFixedInitialEventualExactEntryMass_eq_half
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          leadingOnesFixedInitialEventualExactEntryMass p i x =
      (2 : ENNReal)⁻¹ := by
  rw [← leadingOnesUniformLevelVisitMass_eq_uniform_average_fixedInitialExact
    hp0.le hp1.le i]
  exact leadingOnesUniformLevelVisitMass_eq_half hp0 hp1 i

end ECRuntime
