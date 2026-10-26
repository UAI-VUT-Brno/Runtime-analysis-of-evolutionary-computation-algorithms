import ECRuntime.GeometricPrefixTailRecursion
import ECRuntime.EventLevelFailureCountLocalization
import ECRuntime.LevelExitTrajectory
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 69: direct potential-runtime tail recursion

This module is the central acceleration experiment.  It bypasses the unfinished
multi-coordinate path/failure coupling and proves the finite-state Bellman comparison
directly.

Suppose a bounded natural potential never increases on a positive-probability
transition.  At exact positive level `i+1`, assume the one-step probability of leaving
that exact level is at least `p i`.  Then the probability of avoiding potential zero
for `k` transitions from any state is bounded by the recursive geometric-prefix tail
with as many phases as the current potential value.

The proof uses a support-aware weighted expectation inequality.  Reachable successors
that stay on the current exact level are bounded by the same comparison phase; reachable
successors outside it have potential at most one level lower and are bounded by the
shorter prefix.  The exact-level exit lower bound then gives precisely the geometric
recurrence.
-/

/-- Variant of `weightedExpectation_add_eventMass_mul_le` in which the pointwise
comparison hypotheses are required only on the positive support of the weights.  This
is the correct form for transition-support arguments: unreachable states need not
respect the potential order. -/
theorem weightedExpectation_add_eventMass_mul_le_of_positive_support
    {Omega : Type*} [Fintype Omega]
    (w : Omega -> Real) (event : Omega -> Prop)
    (F : Omega -> Real) (A d : Real)
    (hw : forall omega, 0 <= w omega) (hsum : ∑ omega, w omega = 1)
    (hAll : forall omega, 0 < w omega -> F omega <= A)
    (hEvent : forall omega, 0 < w omega -> event omega -> F omega + d <= A) :
    (∑ omega, w omega * F omega) + d * finiteEventMass w event <= A := by
  classical
  unfold finiteEventMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ omega,
        (w omega * F omega +
          d * (({z | event z} : Set Omega).indicator w omega))) <=
        ∑ omega, w omega * A := by
      apply Finset.sum_le_sum
      intro omega _homega
      by_cases hwzero : w omega = 0
      · by_cases hevent : event omega
        · have hmem : omega ∈ ({z | event z} : Set Omega) := hevent
          rw [Set.indicator_of_mem hmem w, hwzero]
          simp
        · have hnotmem : omega ∉ ({z | event z} : Set Omega) := hevent
          rw [Set.indicator_of_notMem hnotmem w]
          simp [hwzero]
      · have hwpos : 0 < w omega := lt_of_le_of_ne (hw omega) (Ne.symm hwzero)
        by_cases hevent : event omega
        · have hmem : omega ∈ ({z | event z} : Set Omega) := hevent
          rw [Set.indicator_of_mem hmem w]
          calc
            w omega * F omega + d * w omega =
                w omega * (F omega + d) := by ring
            _ <= w omega * A :=
              mul_le_mul_of_nonneg_left
                (hEvent omega hwpos hevent) (hw omega)
        · have hnotmem : omega ∉ ({z | event z} : Set Omega) := hevent
          rw [Set.indicator_of_notMem hnotmem w]
          simp only [mul_zero, add_zero]
          exact mul_le_mul_of_nonneg_left (hAll omega hwpos) (hw omega)
    _ = A := by
      rw [← Finset.sum_mul, hsum]
      ring

/-- Finite positive-potential survival is bounded by the recursive geometric-prefix
comparison tail corresponding to the current potential value. -/
theorem finitePotentialSurvival_le_geometricComparisonTail
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V) :
    forall k x,
      finiteLevelSurvival P ((potentialTarget V)ᶜ) k x <=
        finiteGeometricComparisonTail p (V x) k := by
  intro k
  induction k with
  | zero =>
      intro x
      cases hVx : V x with
      | zero =>
          have hxnot : x ∉ (potentialTarget V)ᶜ := by
            simp [potentialTarget, hVx]
          rw [finiteLevelSurvival_zero_of_not_mem P ((potentialTarget V)ᶜ) x hxnot]
          simp [finiteGeometricComparisonTail]
      | succ n =>
          have hxmem : x ∈ (potentialTarget V)ᶜ := by
            simp [potentialTarget, hVx]
          rw [finiteLevelSurvival_zero_of_mem P ((potentialTarget V)ᶜ) x hxmem]
          simp [finiteGeometricComparisonTail]
  | succ k ih =>
      intro x
      cases hVx : V x with
      | zero =>
          have hxnot : x ∉ (potentialTarget V)ᶜ := by
            simp [potentialTarget, hVx]
          rw [finiteLevelSurvival_succ_of_not_mem
            P ((potentialTarget V)ᶜ) k x hxnot]
          simp [finiteGeometricComparisonTail]
      | succ n =>
          have hnlt : n < m := by
            have hxbound := hbound x
            omega
          let i : Fin m := ⟨n, hnlt⟩
          have hxi : x ∈ exactPositivePotentialLevel V i := by
            change V x = i.val + 1
            simpa [i] using hVx
          have hxmem : x ∈ (potentialTarget V)ᶜ := by
            simp [potentialTarget, hVx]
          rw [finiteLevelSurvival_succ_of_mem
            P ((potentialTarget V)ᶜ) k x hxmem]
          rw [finiteGeometricComparisonTail_succ_succ p n k hnlt]
          let A : Real := finiteGeometricComparisonTail p (n + 1) k
          let B : Real := finiteGeometricComparisonTail p n k
          have hBA : B <= A := by
            exact finiteGeometricComparisonTail_mono_level_of_le
              p hp0 hp1 k (Nat.le_succ n)
          have hdnonneg : 0 <= A - B := sub_nonneg.mpr hBA
          have hAll : forall y, 0 < P x y ->
              finiteLevelSurvival P ((potentialTarget V)ᶜ) k y <= A := by
            intro y hxy
            have hVy : V y <= V x := hmonoP x y hxy
            have htail := ih y
            have hprefix :
                finiteGeometricComparisonTail p (V y) k <= A := by
              dsimp [A]
              apply finiteGeometricComparisonTail_mono_level_of_le p hp0 hp1 k
              simpa [hVx] using hVy
            exact htail.trans hprefix
          have hEvent : forall y, 0 < P x y ->
              y ∉ exactPositivePotentialLevel V i ->
              finiteLevelSurvival P ((potentialTarget V)ᶜ) k y + (A - B) <= A := by
            intro y hxy hyout
            have hVy : V y <= V x := hmonoP x y hxy
            have hVyNe : V y ≠ n + 1 := by
              intro hyEq
              apply hyout
              change V y = i.val + 1
              simpa [i] using hyEq
            have hVyn : V y <= n := by
              omega
            have htail := ih y
            have hprefix :
                finiteGeometricComparisonTail p (V y) k <= B := by
              dsimp [B]
              exact finiteGeometricComparisonTail_mono_level_of_le
                p hp0 hp1 k hVyn
            have hsurvB :
                finiteLevelSurvival P ((potentialTarget V)ᶜ) k y <= B :=
              htail.trans hprefix
            linarith
          have hweighted :
              (∑ y, P x y *
                  finiteLevelSurvival P ((potentialTarget V)ᶜ) k y) +
                  (A - B) * finiteEventMass (P x)
                    (fun y => y ∉ exactPositivePotentialLevel V i) <= A := by
            exact weightedExpectation_add_eventMass_mul_le_of_positive_support
              (P x) (fun y => y ∉ exactPositivePotentialLevel V i)
              (fun y => finiteLevelSurvival P ((potentialTarget V)ᶜ) k y)
              A (A - B) (hP.1 x) (hP.2 x) hAll hEvent
          have hexit_i :
              p i <= finiteEventMass (P x)
                (fun y => y ∉ exactPositivePotentialLevel V i) :=
            hexit i x hxi
          have hfactor :
              (A - B) * p i <=
                (A - B) * finiteEventMass (P x)
                  (fun y => y ∉ exactPositivePotentialLevel V i) :=
            mul_le_mul_of_nonneg_left hexit_i hdnonneg
          have hcore :
              (∑ y, P x y *
                  finiteLevelSurvival P ((potentialTarget V)ᶜ) k y) +
                  (A - B) * p i <= A := by
            exact (add_le_add (le_refl _) hfactor).trans hweighted
          change
            (∑ y, P x y *
                finiteLevelSurvival P ((potentialTarget V)ᶜ) k y) <=
              (1 - p i) * A + p i * B
          nlinarith [hcore]

/-- Uniform version using all `m` positive levels.  This is the exact finite-state
comparison shape required for the conventional fitness-level theorem. -/
theorem finitePotentialSurvival_le_fullGeometricComparisonTail
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (k : Nat) (x : alpha) :
    finiteLevelSurvival P ((potentialTarget V)ᶜ) k x <=
      finiteGeometricComparisonTail p m k := by
  calc
    finiteLevelSurvival P ((potentialTarget V)ᶜ) k x <=
        finiteGeometricComparisonTail p (V x) k :=
      finitePotentialSurvival_le_geometricComparisonTail
        P hP V hbound p hp0 hp1 hexit hmonoP k x
    _ <= finiteGeometricComparisonTail p m k :=
      finiteGeometricComparisonTail_mono_level_of_le
        p hp0 hp1 k (hbound x)

/-- Extensionality of the conventional first-hitting-time observable with respect to
its target set.  The explicit lemma avoids relying on simplification under the
`DecidablePred` instance carried by `transitionTrajectoryFirstHittingTime`. -/
private theorem transitionTrajectoryFirstHittingTime_congr_target
    {alpha : Type*}
    (s t : Set alpha)
    [hs : DecidablePred (fun z => z ∈ s)]
    [ht : DecidablePred (fun z => z ∈ t)]
    (hst : s = t) (x : alpha) :
    transitionTrajectoryFirstHittingTime s x =
      transitionTrajectoryFirstHittingTime t x := by
  subst t
  have hdec : hs = ht := by
    funext z
    exact Subsingleton.elim (hs z) (ht z)
  cases hdec
  rfl

/-- Natural-threshold tail mass of the conventional zero-potential hitting time is the
positive-potential finite survival mass. -/
theorem transitionTrajectoryPotentialHittingTime_tailMass_eq_finitePotentialSurvival
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (k : Nat) :
    runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
        (k : ENNReal) =
      ENNReal.ofReal
        (finiteLevelSurvival P ((potentialTarget V)ᶜ) k x) := by
  have htarget : ((potentialTarget V)ᶜ)ᶜ = potentialTarget V := by
    ext z
    simp
  have hhit :
      transitionTrajectoryFirstHittingTime (((potentialTarget V)ᶜ)ᶜ) x =
        transitionTrajectoryFirstHittingTime (potentialTarget V) x :=
    transitionTrajectoryFirstHittingTime_congr_target
      (((potentialTarget V)ᶜ)ᶜ) (potentialTarget V) htarget x
  rw [← hhit]
  exact transitionTrajectoryLevelExit_tailMass_eq_finiteLevelSurvival
    P ((potentialTarget V)ᶜ) hP x k

/-- Direct trajectory-level tail bound by the full recursive geometric comparison
table.  No adaptive multi-coordinate coupling is used. -/
theorem transitionTrajectoryPotentialHittingTime_tailMass_le_geometricComparisonTail
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : alpha) (k : Nat) :
    runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime (potentialTarget V) x)
        (k : ENNReal) <=
      ENNReal.ofReal (finiteGeometricComparisonTail p m k) := by
  rw [transitionTrajectoryPotentialHittingTime_tailMass_eq_finitePotentialSurvival
    P hP V x k]
  exact ENNReal.ofReal_le_ofReal
    (finitePotentialSurvival_le_fullGeometricComparisonTail
      P hP V hbound p hp0 hp1 hexit hmonoP k x)

end ECRuntime
