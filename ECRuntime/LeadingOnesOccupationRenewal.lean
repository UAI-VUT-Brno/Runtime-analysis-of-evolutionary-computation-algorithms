import ECRuntime.LeadingOnesLevelChargeOccupation
import Mathlib

open scoped BigOperators ENNReal
open Finset

namespace ECRuntime

/-!
# Stage 27 fix 20: local renewal ingredients for one LeadingOnes score level

Stage 27 fix 19 fix 2 is compiler verified warning/error-free.  In particular, for a
fixed initial state `x` and score level `i`, the expected complete score-level charge is
now exactly the total occupation mass

  `sup_T sum_{t<T} P_x(LO(X_t)=i)`.

The remaining probabilistic identity is a renewal statement.  If
`q_i = p * (1-p)^i`, occupation at time `t+1` consists of either a new first entry at
`t+1` or occupation at time `t` followed by one stay in the same score level, whose
mass is `1-q_i`.  Elitist selection also rules out any return to score `i` after the
process has moved strictly above it.

This module isolates exactly those local ingredients and the scalar algebra of the
resulting recurrence.  It deliberately does not assert the concrete trajectory-level
recurrence yet: the next slice only has to identify the lower-score contribution in the
one-step marginal recursion with the already promoted exact first-entry slice.
-/

/-- Every positive-probability LeadingOnes transition weakly increases the score. -/
theorem onePlusOneTransition_leadingOnes_score_mono_of_pos
    {n : ℕ} (p : ℝ) (x y : BitString n)
    (hxy : 0 < onePlusOneTransition p (leadingOnesReal (n := n)) x y) :
    leadingOnes x ≤ leadingOnes y := by
  have hpot :=
    onePlusOneTransition_leadingOnes_hasPotentialNonincreasingTransitionSupport
      (n := n) p x y hxy
  have hx := leadingOnes_le x
  have hy := leadingOnes_le y
  unfold leadingOnesPotential at hpot
  omega

/-- Once the current score is strictly above `i`, one transition has zero mass of
returning to score level `i`. -/
theorem onePlusOneTransition_leadingOnes_aboveLevel_scoreMass_eq_zero
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n)
    (habove : i.val < leadingOnes x) :
    finiteEventMass
        (onePlusOneTransition p (leadingOnesReal (n := n)) x)
        (fun y => leadingOnes y = i.val) = 0 := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  change finiteEventMass (P x) (fun y => leadingOnes y = i.val) = 0
  unfold finiteEventMass
  apply Finset.sum_eq_zero
  intro y _hy
  by_cases hlevel : leadingOnes y = i.val
  · have hnotpos : ¬ 0 < P x y := by
      intro hpos
      have hmono : leadingOnes x ≤ leadingOnes y := by
        exact onePlusOneTransition_leadingOnes_score_mono_of_pos
          (n := n) p x y hpos
      rw [hlevel] at hmono
      omega
    have hzero : P x y = 0 := by
      exact le_antisymm (le_of_not_gt hnotpos) (hP.1 x y)
    simp [hlevel, hzero]
  · simp [hlevel]

/-- The one-step mass of staying in a visited LeadingOnes score level is exactly
`1-q_i`, where `q_i = p(1-p)^i` is the promoted exact exit mass. -/
theorem onePlusOneTransition_leadingOnes_exactLevel_stayMass_eq
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    finiteEventMass
        (onePlusOneTransition p (leadingOnesReal (n := n)) x)
        (fun y => leadingOnes y = i.val) =
      1 - leadingOnesLevelExitProbability p i := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have hpartition := finiteEventMass_add_compl (P x) (fun y => leadingOnes y = i.val)
  have hrow : (∑ y, P x y) = 1 := hP.2 x
  have hexit :
      finiteEventMass (P x) (fun y => leadingOnes y ≠ i.val) =
        leadingOnesLevelExitProbability p i := by
    unfold leadingOnesLevelExitProbability
    exact onePlusOneTransition_leadingOnes_exactLevel_exitMass_eq
      p x i hlevel
  rw [hrow, hexit] at hpartition
  linarith

/-- `ENNReal` form of the exact one-step stay factor used in the occupation renewal. -/
noncomputable def leadingOnesLevelStayENNReal
    {n : ℕ} (p : ℝ) (i : Fin n) : ENNReal :=
  ENNReal.ofReal (1 - leadingOnesLevelExitProbability p i)

/-- Exact-entry mass at one time, embedded in the same scalar type as occupation mass. -/
noncomputable def leadingOnesFixedInitialExactEntryENNMass
    {n : ℕ} (p : ℝ) (i : Fin n) (x : BitString n) (t : ℕ) : ENNReal :=
  ENNReal.ofReal
    (leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x)

/-- Abstract scalar renewal equation used by the final fixed-level proof. -/
def HasScalarRenewalRecurrence
    {R : Type*} [CommSemiring R]
    (entry occupation : ℕ → R) (stay : R) : Prop :=
  occupation 0 = entry 0 ∧
    ∀ t : ℕ, occupation (t + 1) = entry (t + 1) + stay * occupation t

/-- A scalar sequence satisfying the one-step renewal equation is the finite convolution
of entry masses with powers of the stay factor. -/
theorem scalarRenewalRecurrence_eq_convolution
    {R : Type*} [CommSemiring R]
    (entry occupation : ℕ → R) (stay : R)
    (hrenew : HasScalarRenewalRecurrence entry occupation stay) :
    ∀ t : ℕ,
      occupation t =
        ∑ s ∈ Finset.range (t + 1), entry s * stay ^ (t - s) := by
  intro t
  induction t with
  | zero =>
      calc
        occupation 0 = entry 0 := hrenew.1
        _ = ∑ s ∈ Finset.range (0 + 1), entry s * stay ^ (0 - s) := by
          simp
  | succ t ih =>
      have hstep := hrenew.2 t
      have hsum :
          stay *
              (∑ s ∈ Finset.range (t + 1),
                entry s * stay ^ (t - s)) =
            ∑ s ∈ Finset.range (t + 1),
              entry s * stay ^ ((t + 1) - s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        have hslt : s < t + 1 := Finset.mem_range.mp hs
        have hsub : (t + 1) - s = (t - s) + 1 := by
          omega
        rw [hsub, pow_succ]
        ac_rfl
      calc
        occupation (t + 1) =
            entry (t + 1) + stay * occupation t := hstep
        _ = entry (t + 1) +
            stay *
              (∑ s ∈ Finset.range (t + 1),
                entry s * stay ^ (t - s)) := by
              rw [ih]
        _ = entry (t + 1) +
            ∑ s ∈ Finset.range (t + 1),
              entry s * stay ^ ((t + 1) - s) := by
              rw [hsum]
        _ = (∑ s ∈ Finset.range (t + 1),
              entry s * stay ^ ((t + 1) - s)) +
            entry (t + 1) * stay ^ 0 := by
              simp [add_comm]
        _ = ∑ s ∈ Finset.range ((t + 1) + 1),
              entry s * stay ^ ((t + 1) - s) := by
              symm
              rw [Finset.sum_range_succ]
              simp

/-- Concrete recurrence predicate for one fixed initial LeadingOnes score level.  This
is the only stochastic statement left after the local transition facts above. -/
def HasLeadingOnesFixedInitialScoreLevelOccupationRenewal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) : Prop :=
  HasScalarRenewalRecurrence
    (fun t => leadingOnesFixedInitialExactEntryENNMass p i x t)
    (fun t => leadingOnesFixedInitialScoreLevelOccupationMass
      p hp0 hp1 x i t)
    (leadingOnesLevelStayENNReal p i)

/-- Once the concrete fixed-initial renewal recurrence is established, every exact-time
occupation mass has the expected first-entry/geometric convolution form. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_eq_entryConvolution_of_renewal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n)
    (hrenew : HasLeadingOnesFixedInitialScoreLevelOccupationRenewal
      p hp0 hp1 x i)
    (t : ℕ) :
    leadingOnesFixedInitialScoreLevelOccupationMass
        p hp0 hp1 x i t =
      ∑ s ∈ Finset.range (t + 1),
        leadingOnesFixedInitialExactEntryENNMass p i x s *
          (leadingOnesLevelStayENNReal p i) ^ (t - s) := by
  exact scalarRenewalRecurrence_eq_convolution
    (fun s => leadingOnesFixedInitialExactEntryENNMass p i x s)
    (fun s => leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i s)
    (leadingOnesLevelStayENNReal p i) hrenew t

end ECRuntime
