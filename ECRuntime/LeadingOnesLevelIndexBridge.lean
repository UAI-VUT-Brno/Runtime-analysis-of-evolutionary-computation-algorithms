import ECRuntime.LeadingOnesTrajectoryMonotonicity
import Mathlib

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 16: align LeadingOnes score levels with distance-potential charges

Stage 27 fix 15 is compiler verified warning/error-free.  Its exact residence theorem
turns a complete charge of positive potential level `j+1` into the length of the unique
residence interval at that potential level.  The exact LeadingOnes exit/residence law
from fixes 10--11, however, is naturally indexed by objective score level `i`, where

  `leadingOnes x = i`.

For the canonical distance potential

  `leadingOnesPotential x = n - leadingOnes x`,

these two finite indexings run in opposite directions.  Score level `i` corresponds to
positive-potential coordinate

  `n - (i+1)`,

because potential value `n-i` is represented by charge coordinate
`n-(i+1)`.  The distinction was harmless while the two sides of the exact-runtime
argument were developed separately, but it must be explicit before their expectations
are identified.

This module packages the reversal as a self-equivalence of `Fin n`, proves the exact
state-level correspondence, reindexes arbitrary finite sums, and rewrites both the
pathwise and the genuine uniform-initialization charge representations into the score
index used by the promoted factor `p * (1-p)^i`.

No probability factorization is claimed here.  After this indexing bridge is compiler
verified, each score-indexed charge can be matched to the first-entry/residence law for
the *same* `i` without a hidden reversal.
-/

/-- Positive-potential charge coordinate corresponding to LeadingOnes score level `i`.
The map reverses the finite order `0, ..., n-1`. -/
def leadingOnesScoreToPotentialIndex {n : Nat} (i : Fin n) : Fin n :=
  ⟨n - (i.val + 1), by
    have hi : i.val < n := i.isLt
    omega⟩

/-- Reversing score/potential indices twice returns the original index. -/
@[simp] theorem leadingOnesScoreToPotentialIndex_involutive
    {n : Nat} (i : Fin n) :
    leadingOnesScoreToPotentialIndex
        (leadingOnesScoreToPotentialIndex i) = i := by
  have hi : i.val < n := i.isLt
  apply Fin.ext
  dsimp [leadingOnesScoreToPotentialIndex]
  omega

/-- The score-level / positive-potential-coordinate reversal as an explicit equivalence. -/
def leadingOnesScorePotentialIndexEquiv (n : Nat) : Fin n ≃ Fin n where
  toFun := leadingOnesScoreToPotentialIndex
  invFun := leadingOnesScoreToPotentialIndex
  left_inv := by
    intro i
    exact leadingOnesScoreToPotentialIndex_involutive i
  right_inv := by
    intro i
    exact leadingOnesScoreToPotentialIndex_involutive i

@[simp] theorem leadingOnesScorePotentialIndexEquiv_apply
    {n : Nat} (i : Fin n) :
    leadingOnesScorePotentialIndexEquiv n i =
      leadingOnesScoreToPotentialIndex i := by
  rfl

/-- A state has LeadingOnes score `i` iff its canonical distance potential occupies the
positive-potential charge coordinate obtained by reversing `i`. -/
theorem leadingOnesPotential_eq_scoreIndex_succ_iff
    {n : Nat} (x : BitString n) (i : Fin n) :
    leadingOnesPotential x =
        (leadingOnesScoreToPotentialIndex i).val + 1 ↔
      leadingOnes x = i.val := by
  have hx : leadingOnes x ≤ n := leadingOnes_le x
  have hi : i.val < n := i.isLt
  change n - leadingOnes x = (n - (i.val + 1)) + 1 ↔
    leadingOnes x = i.val
  omega

/-- The generic one-hot positive-potential indicator at the reversed coordinate is
exactly the indicator of LeadingOnes score level `i`. -/
theorem positiveLevelIndicator_leadingOnesPotential_scoreIndex
    {n : Nat} (x : BitString n) (i : Fin n) :
    positiveLevelIndicator (leadingOnesPotential x)
        (leadingOnesScoreToPotentialIndex i) =
      if leadingOnes x = i.val then 1 else 0 := by
  by_cases hlevel : leadingOnes x = i.val
  · have hpot :=
      (leadingOnesPotential_eq_scoreIndex_succ_iff x i).2 hlevel
    simp [positiveLevelIndicator, hlevel, hpot]
  · have hpot :
        leadingOnesPotential x ≠
          (leadingOnesScoreToPotentialIndex i).val + 1 := by
      intro h
      exact hlevel ((leadingOnesPotential_eq_scoreIndex_succ_iff x i).1 h)
    simp [positiveLevelIndicator, hlevel, hpot]

/-- Reindex an arbitrary finite sum from positive-potential coordinates to LeadingOnes
score coordinates. -/
theorem sum_leadingOnesScoreToPotentialIndex
    {n : Nat} {β : Type*} [AddCommMonoid β]
    (f : Fin n -> β) :
    (∑ j : Fin n, f j) =
      ∑ i : Fin n, f (leadingOnesScoreToPotentialIndex i) := by
  classical
  symm
  refine Fintype.sum_equiv (leadingOnesScorePotentialIndexEquiv n)
    (fun i : Fin n => f (leadingOnesScoreToPotentialIndex i)) f ?_
  intro i
  rfl

/-- Exact pathwise runtime decomposition indexed by LeadingOnes score rather than by
positive distance-potential value. -/
theorem leadingOnesFirstHittingTime_eq_scoreIndexedLevelChargeSum_of_nonincreasing
    {n : Nat} (x : BitString n) (path : Nat -> BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path) :
    transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path =
      ∑ i : Fin n,
        trajectoryLevelCharge (leadingOnesPotential (n := n)) x
          (leadingOnesScoreToPotentialIndex i) path := by
  calc
    transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path =
        ∑ j : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x j path :=
      leadingOnesFirstHittingTime_eq_levelChargeSum_of_nonincreasing
        x path hmono
    _ = ∑ i : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x
            (leadingOnesScoreToPotentialIndex i) path :=
      sum_leadingOnesScoreToPotentialIndex
        (fun j : Fin n =>
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x j path)

/-- Fixed-initial expectation representation with level charges indexed by the same
LeadingOnes score coordinate used by the exact exit/residence law. -/
theorem leadingOnesFixedInitialFirstHittingTimeExpectation_eq_scoreIndexedLevelChargeExpectation
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n) :
    (∫⁻ path : Nat -> BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      ∫⁻ path : Nat -> BitString n,
        ∑ i : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x
            (leadingOnesScoreToPotentialIndex i) path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
  rw [leadingOnesFixedInitialFirstHittingTimeExpectation_eq_levelChargeExpectation
    p hp0 hp1 x]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun path =>
    sum_leadingOnesScoreToPotentialIndex
      (fun j : Fin n =>
        trajectoryLevelCharge (leadingOnesPotential (n := n)) x j path))

/-- Uniform-initialization expectation representation after the score/potential index
alignment.  This is the measure-level starting point for the remaining one-level
first-entry times residence factorization. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_scoreIndexedLevelChargeExpectation
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0 hp1 =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          ∫⁻ path : Nat -> BitString n,
            ∑ i : Fin n,
              trajectoryLevelCharge (leadingOnesPotential (n := n)) x
                (leadingOnesScoreToPotentialIndex i) path
          ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_eq_levelChargeExpectation
    n p hp0 hp1]
  apply congrArg
    (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro x _hx
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun path =>
    sum_leadingOnesScoreToPotentialIndex
      (fun j : Fin n =>
        trajectoryLevelCharge (leadingOnesPotential (n := n)) x j path))

end ECRuntime
