import ECRuntime.LeadingOnesOccupationTotalClosure
import ECRuntime.LeadingOnesRuntimeChargeDecomposition
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 169 candidate: intermediate fixed-target LeadingOnes runtime

Source direction: Buzdalov--Doerr--Doerr--Vinokurov, *Fixed-Target Runtime
Analysis*, the LeadingOnes fixed-target family (Theorem 4 in arXiv v3).

This is the (1+1)-EA independent-bit-mutation, uniform-initialization subcase.
It is NOT a claim about all algorithms or initialization laws treated by the
source paper. The full-target case `k = n` already follows from the verified
LeadingOnes occupation proof. The proposed generalization truncates level
charges at score `k` and requires an actual hitting-time/occupation bridge.

The paper-facing theorem was approved by the user. Its final expected-runtime
bridge now has an admission-free proof attempt; compiler elaboration, axiom
checks, and eight-gate promotion remain required. Supporting pathwise lemmas
are proof candidates until compiler verified. Nothing in this
file is promoted by its presence in `candidates/`.
-/

/-- Fixed LeadingOnes target: attain at least `k` consecutive leading one
bits. When `k = 0`, the target is the entire search space. -/
def leadingOnesAtLeast {n : ℕ} (k : ℕ) : Set (BitString n) :=
  {x | k ≤ leadingOnes x}

/-- Fixed-target membership is decidable directly from the score. -/
instance instDecidablePredLeadingOnesAtLeast {n : ℕ} (k : ℕ) :
    DecidablePred (fun x : BitString n => x ∈ leadingOnesAtLeast k) := by
  intro x
  change Decidable (k ≤ leadingOnes x)
  infer_instance

/-- Uniform-start real mean hitting time for reaching LeadingOnes score `k`.
It counts mutation iterations and is defined as a finite arithmetic average
of `runtimeSup.toReal`, not as an integral over trajectory measures. -/
noncomputable def leadingOnesUniformFixedTargetMean
    (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.sum (fun x : BitString n =>
    (runtimeSup
      (onePlusOneTransition p (leadingOnesReal (n := n)))
      (leadingOnesAtLeast (n := n) k) x).toReal)) / (2 : ℝ) ^ n

/-! The fixed-target formula cannot be obtained merely by truncating the
closed full-optimization formula. We first prove the *pathwise* bookkeeping
bridge for the truncated potential. The remaining admission is precisely the
probabilistic mean-occupation statement for these charges. -/

/-- Distance to an intermediate LeadingOnes target. -/
def leadingOnesFixedTargetPotential {n : ℕ} (k : ℕ)
    (x : BitString n) : ℕ :=
  k - leadingOnes x

/-- The target is the zero set of the truncated potential, including `k=0`. -/
theorem leadingOnesFixedTargetPotential_target_eq
    {n : ℕ} (k : ℕ) :
    potentialTarget (leadingOnesFixedTargetPotential (n := n) k) =
      leadingOnesAtLeast (n := n) k := by
  ext x
  change (k - leadingOnes x = 0) ↔ k ≤ leadingOnes x
  omega

/-- Truncation preserves the monotonicity needed for pathwise accounting. -/
theorem leadingOnesFixedTargetPotential_nonincreasing
    {n : ℕ} (k : ℕ) (x : BitString n) (path : ℕ → BitString n)
    (hscore : ∀ t : ℕ,
      leadingOnes (transitionTrajectoryState x path t) ≤
        leadingOnes (transitionTrajectoryState x path (t + 1))) :
    IsPotentialNonincreasingAlong
      (leadingOnesFixedTargetPotential k) x path := by
  intro t
  change k - leadingOnes (transitionTrajectoryState x path (t + 1)) ≤
    k - leadingOnes (transitionTrajectoryState x path t)
  have ht := hscore t
  omega

/-- Exact deterministic time decomposition for the truncated potential.
Every nonterminal fixed-target trajectory is charged to exactly one of the
`k` positive potential levels; no suffix independence is used here. -/
theorem leadingOnesFixedTargetPotential_pathwise_charge
    {n : ℕ} (k : ℕ) (x : BitString n) (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesFixedTargetPotential k) x path) :
    transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesFixedTargetPotential k)) x path =
      ∑ i : Fin k,
        trajectoryLevelCharge (leadingOnesFixedTargetPotential k) x i path := by
  have hbound : ∀ y : BitString n,
      leadingOnesFixedTargetPotential k y ≤ k := by
    intro y
    exact Nat.sub_le _ _
  simpa only [finiteRuntimeSum] using
    (transitionTrajectoryFirstHittingTime_eq_levelChargeSum_of_nonincreasing
      (leadingOnesFixedTargetPotential k) hbound x path hmono)

/-- The truncated potential's positive coordinate corresponding to a score
`i < k` is exactly the same score indicator as the full distance potential.
The coordinate map reverses `Fin k`; no probabilistic premise is used. -/
theorem leadingOnesFixedTargetPotential_eq_scoreIndex_succ_iff
    {n : ℕ} (k : ℕ) (x : BitString n) (i : Fin k) :
    leadingOnesFixedTargetPotential k x =
        (leadingOnesScoreToPotentialIndex i).val + 1 ↔
      leadingOnes x = i.val := by
  have hi : i.val < k := i.isLt
  change k - leadingOnes x = (k - (i.val + 1)) + 1 ↔
    leadingOnes x = i.val
  omega

/-- For any fixed target `k ≤ n`, a score-indexed truncated level is
pointwise identical to the corresponding score-indexed full-runtime level.
This identifies the appropriate one-level occupation observable. -/
theorem leadingOnesFixedTargetPotential_scoreIndicator_eq
    {n : ℕ} (k : ℕ) (hk : k ≤ n) (y : BitString n) (i : Fin k) :
    positiveLevelIndicator (leadingOnesFixedTargetPotential k y)
        (leadingOnesScoreToPotentialIndex i) =
      positiveLevelIndicator (leadingOnesPotential y)
        (leadingOnesScoreToPotentialIndex (i.castLE hk)) := by
  -- Avoid rewriting through a dependent `Fin.castLE` term: compare both
  -- propositions in the two underlying one-hot indicators explicitly.
  classical
  have hcond :
      (leadingOnesFixedTargetPotential k y =
          (leadingOnesScoreToPotentialIndex i).val + 1) ↔
        (leadingOnesPotential y =
          (leadingOnesScoreToPotentialIndex (i.castLE hk)).val + 1) := by
    constructor
    · intro h
      apply (leadingOnesPotential_eq_scoreIndex_succ_iff
        y (i.castLE hk)).2
      simpa only [Fin.val_castLE] using
        (leadingOnesFixedTargetPotential_eq_scoreIndex_succ_iff k y i).1 h
    · intro h
      apply (leadingOnesFixedTargetPotential_eq_scoreIndex_succ_iff k y i).2
      have hs := (leadingOnesPotential_eq_scoreIndex_succ_iff
        y (i.castLE hk)).1 h
      simpa only [Fin.val_castLE] using hs
  unfold positiveLevelIndicator
  by_cases hc : leadingOnesFixedTargetPotential k y =
      (leadingOnesScoreToPotentialIndex i).val + 1
  · have hd := hcond.mp hc
    simp [hc, hd]
  · have hd : ¬ leadingOnesPotential y =
        (leadingOnesScoreToPotentialIndex (i.castLE hk)).val + 1 := by
      intro h
      exact hc (hcond.mpr h)
    simp [hc, hd]

/-- Consequently the full infinite-path residence charge for score `i < k`
is *unchanged* when the terminal target moves from `n` to `k`.
Visits at score `i` cannot occur after reaching `k` on a monotone path;
this lemma is a pointwise equality of indicators, independent of monotonicity. -/
theorem leadingOnesFixedTargetPotential_scoreCharge_eq
    {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : BitString n)
    (i : Fin k) (path : ℕ → BitString n) :
    trajectoryLevelCharge (leadingOnesFixedTargetPotential k) x
        (leadingOnesScoreToPotentialIndex i) path =
      trajectoryLevelCharge (leadingOnesPotential (n := n)) x
        (leadingOnesScoreToPotentialIndex (i.castLE hk)) path := by
  unfold trajectoryLevelCharge finiteHorizonLevelCharge
  apply iSup_congr
  intro T
  apply Finset.sum_congr rfl
  intro t _ht
  exact leadingOnesFixedTargetPotential_scoreIndicator_eq
    k hk (transitionTrajectoryState x path t) i

/-- Every nondecreasing score trajectory also decreases the truncated
fixed-target potential, even when it skips directly across the target. -/
theorem leadingOnesFixedTargetPotential_nonincreasing_of_full
    {n : ℕ} (k : ℕ) (x : BitString n)
    (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path) :
    IsPotentialNonincreasingAlong
      (leadingOnesFixedTargetPotential k) x path := by
  intro t
  have hprev := leadingOnes_le (transitionTrajectoryState x path t)
  have hnext := leadingOnes_le (transitionTrajectoryState x path (t + 1))
  have hstep := hmono t
  change n - leadingOnes (transitionTrajectoryState x path (t + 1)) ≤
    n - leadingOnes (transitionTrajectoryState x path t) at hstep
  change k - leadingOnes (transitionTrajectoryState x path (t + 1)) ≤
    k - leadingOnes (transitionTrajectoryState x path t)
  omega

/-- The fixed-target hitting time is exactly the sum of *existing*
LeadingOnes score-indexed occupation charges below the target.  This is the
pathwise reduction of fixed-target analysis to the previously certified
full-target occupation family. -/
theorem leadingOnesFixedTarget_firstHittingTime_eq_scoreIndexedChargeSum
    {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : BitString n)
    (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path) :
    transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesFixedTargetPotential k)) x path =
      ∑ i : Fin k,
        trajectoryLevelCharge (leadingOnesPotential (n := n)) x
          (leadingOnesScoreToPotentialIndex (i.castLE hk)) path := by
  calc
    transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesFixedTargetPotential k)) x path =
        ∑ j : Fin k,
          trajectoryLevelCharge (leadingOnesFixedTargetPotential k) x
            j path :=
      leadingOnesFixedTargetPotential_pathwise_charge k x path
        (leadingOnesFixedTargetPotential_nonincreasing_of_full k x path hmono)
    _ = ∑ i : Fin k,
          trajectoryLevelCharge (leadingOnesFixedTargetPotential k) x
            (leadingOnesScoreToPotentialIndex i) path :=
      sum_leadingOnesScoreToPotentialIndex
        (fun j : Fin k =>
          trajectoryLevelCharge (leadingOnesFixedTargetPotential k) x j path)
    _ = ∑ i : Fin k,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x
            (leadingOnesScoreToPotentialIndex (i.castLE hk)) path := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact leadingOnesFixedTargetPotential_scoreCharge_eq k hk x i path

/-! ### The measure-level fixed-target bridge

The prior certified full-target argument already computes the expectation of
*each* score-level occupation charge. Only the number of levels whose charges
are summed changes when the target is a strict intermediate prefix length.
The following intermediate result is deliberately `ENNReal`-valued: it avoids
identifying `toReal` with an expectation before proving finiteness.
-/

/-- The finite sum over scores `Fin k` equals the canonical integer-range
sum used by the approved fixed-target theorem statement. -/
private theorem stage169_sum_fin_val_eq_range (k : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin k, f i.val) = (Finset.range k).sum f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, Finset.sum_range_succ]
      simpa only [Fin.val_castSucc, Fin.val_last] using
        congrArg (fun z : ℝ => z + f k) ih

/-- Exact uniformly initialized fixed-target sample-path expectation. -/
noncomputable def leadingOnesUniformFixedTargetENNMean
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : ENNReal :=
  ((Fintype.card (BitString n) : ENNReal)⁻¹) *
    ∑ x : BitString n,
      ∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime
          (leadingOnesAtLeast (n := n) k) x path
        ∂leadingOnesTrajectoryMeasure p hp0 hp1 x

/-- Transfer the deterministic fixed-target score-charge equality to the
actual infinite-path law and interchange its finite sums with lintegral.
It is important that the score-charge integrands are already certified
measurable: no independence hypothesis is introduced here. -/
theorem leadingOnesUniformFixedTargetENNMean_eq_scoreCharges
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (hk : k ≤ n) :
    leadingOnesUniformFixedTargetENNMean n p hp0 hp1 k =
      ∑ i : Fin k,
        leadingOnesUniformScoreLevelChargeExpectation
          n p hp0 hp1 (i.castLE hk) := by
  classical
  have hpoint (x : BitString n) :
      (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime
          (leadingOnesAtLeast (n := n) k) x path
        ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      ∑ i : Fin k,
        leadingOnesFixedInitialScoreLevelChargeExpectation
          p hp0 hp1 x (i.castLE hk) := by
    calc
      (∫⁻ path : ℕ → BitString n,
          transitionTrajectoryFirstHittingTime
            (leadingOnesAtLeast (n := n) k) x path
          ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
        ∫⁻ path : ℕ → BitString n,
          ∑ i : Fin k,
            trajectoryLevelCharge (leadingOnesPotential (n := n)) x
              (leadingOnesScoreToPotentialIndex (i.castLE hk)) path
          ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
        apply lintegral_congr_ae
        filter_upwards [leadingOnesTrajectoryMeasure_ae_potentialNonincreasing
          p hp0 hp1 x] with path hmono
        simpa only [leadingOnesFixedTargetPotential_target_eq] using
          (leadingOnesFixedTarget_firstHittingTime_eq_scoreIndexedChargeSum
            k hk x path hmono)
      _ = ∑ i : Fin k,
            leadingOnesFixedInitialScoreLevelChargeExpectation
              p hp0 hp1 x (i.castLE hk) := by
        simpa only [leadingOnesFixedInitialScoreLevelChargeExpectation] using
          (MeasureTheory.lintegral_finsetSum
            (μ := leadingOnesTrajectoryMeasure p hp0 hp1 x)
            (s := (Finset.univ : Finset (Fin k)))
            (f := fun (i : Fin k) (path : ℕ → BitString n) =>
              trajectoryLevelCharge (leadingOnesPotential (n := n)) x
                (leadingOnesScoreToPotentialIndex (i.castLE hk)) path)
            (by
              intro i _hi
              exact measurable_leadingOnesScoreIndexedLevelCharge
                x (i.castLE hk)))
  calc
    leadingOnesUniformFixedTargetENNMean n p hp0 hp1 k =
        ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          ∑ x : BitString n,
            ∑ i : Fin k,
              leadingOnesFixedInitialScoreLevelChargeExpectation
                p hp0 hp1 x (i.castLE hk) := by
      unfold leadingOnesUniformFixedTargetENNMean
      apply congrArg
        (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
      exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = ∑ i : Fin k,
          leadingOnesUniformScoreLevelChargeExpectation
            n p hp0 hp1 (i.castLE hk) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      rfl

/-- An exact intermediate-target formula in extended nonnegative reals.
Because the right side is finite, the theorem also provides a finiteness
certificate for the averaged hitting time. -/
theorem leadingOnesUniformFixedTargetENNMean_eq_formula
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hk : k ≤ n) :
    leadingOnesUniformFixedTargetENNMean n p hp0.le hp1.le k =
      ENNReal.ofReal
        ((1 / 2 : ℝ) *
          (Finset.range k).sum (fun i => (p * (1 - p) ^ i)⁻¹)) := by
  classical
  rw [leadingOnesUniformFixedTargetENNMean_eq_scoreCharges
    p hp0.le hp1.le k hk]
  have hnonneg (i : Fin k) :
      0 ≤ (1 / 2 : ℝ) * (p * (1 - p) ^ i.val)⁻¹ := by
    have hres := leadingOnesVisitedLevelMeanResidence_nonneg
      hp0 hp1 (i.castLE hk)
    simpa only [leadingOnesVisitedLevelMeanResidence,
      leadingOnesLevelExitProbability, Fin.val_castLE] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hres
  calc
    (∑ i : Fin k,
        leadingOnesUniformScoreLevelChargeExpectation
          n p hp0.le hp1.le (i.castLE hk)) =
      ∑ i : Fin k,
        ENNReal.ofReal ((1 / 2 : ℝ) * (p * (1 - p) ^ i.val)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [leadingOnesVisitedLevelMeanResidence,
        leadingOnesLevelExitProbability, Fin.val_castLE] using
          (leadingOnesUniformScoreLevelChargeExpectation_eq_residenceContribution
            hp0 hp1 (i.castLE hk)).trans
          (leadingOnesUniformLevelResidenceContribution_eq_ofReal_half_mean
            hp0 hp1 (i.castLE hk))
    _ = ENNReal.ofReal
          (∑ i : Fin k,
            (1 / 2 : ℝ) * (p * (1 - p) ^ i.val)⁻¹) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)).symm
    _ = ENNReal.ofReal
          ((1 / 2 : ℝ) * ∑ i : Fin k, (p * (1 - p) ^ i.val)⁻¹) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal
          ((1 / 2 : ℝ) *
            (Finset.range k).sum (fun i => (p * (1 - p) ^ i)⁻¹)) := by
      exact congrArg
        (fun z : ℝ => ENNReal.ofReal ((1 / 2 : ℝ) * z))
        (stage169_sum_fin_val_eq_range k
          (fun i : ℕ => (p * (1 - p) ^ i)⁻¹))

/-- The very same extended expectation is the uniform Bellman `runtimeSup`
average, by the certified general hitting-time/`runtimeSup` identity. -/
theorem leadingOnesUniformFixedTargetENNMean_eq_runtimeSup_average
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    leadingOnesUniformFixedTargetENNMean n p hp0 hp1 k =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          runtimeSup
            (onePlusOneTransition p (leadingOnesReal (n := n)))
            (leadingOnesAtLeast (n := n) k) x := by
  classical
  unfold leadingOnesUniformFixedTargetENNMean
  apply congrArg
    (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro x _
  unfold leadingOnesTrajectoryMeasure
  exact transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
    (onePlusOneTransition p (leadingOnesReal (n := n)))
    (leadingOnesAtLeast (n := n) k)
    (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))) x


/-! ### Extended-real / real finite-uniform-average bridge

The extended-real expectation theorem is not by itself a statement about the
arithmetic average of the statewise `runtimeSup.toReal` values. At top,
`ENNReal.toReal` returns zero; therefore we prove the finiteness of *every*
statewise runtime from the finiteness of the positive-weighted extended-real
average before moving `ENNReal.ofReal` through the finite sum.
-/

/-- A finite positive-weight uniform average can be converted from `ENNReal`
to an arithmetic mean of `toReal` values if it has an exact finite real
expression. The `Nonempty` hypothesis rules out a zero cardinality factor.
There is no assumption that the summands are finite: that fact is derived
from the equality to a finite `ofReal` value. -/
private theorem stage169_finite_uniform_ennreal_average_toReal
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ENNReal) (R : ℝ) (hR : 0 ≤ R)
    (havg :
      ((Fintype.card α : ENNReal)⁻¹) * (∑ x : α, f x) =
        ENNReal.ofReal R) :
    (∑ x : α, (f x).toReal) / (Fintype.card α : ℝ) = R := by
  classical
  have hcardReal : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hcardNonzero : (Fintype.card α : ℕ) ≠ 0 := Fintype.card_ne_zero
  have hcardNotTop : (Fintype.card α : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hinvNonzero : ((Fintype.card α : ENNReal)⁻¹) ≠ 0 := by
    simp [hcardNotTop]
  have hsumNotTop : (∑ x : α, f x) ≠ ⊤ := by
    intro htop
    have hbad : ENNReal.ofReal R = ⊤ := by
      calc
        ENNReal.ofReal R =
            ((Fintype.card α : ENNReal)⁻¹) * (∑ x : α, f x) := havg.symm
        _ = ⊤ := by simp [htop, hinvNonzero]
    exact ENNReal.ofReal_ne_top hbad
  have htermNotTop : ∀ x : α, f x ≠ ⊤ := by
    intro x hx
    have hle : f x ≤ ∑ y : α, f y :=
      Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ x)
    have htop : (∑ y : α, f y) = ⊤ := by
      apply le_antisymm le_top
      simpa [hx] using hle
    exact hsumNotTop htop
  have hsumNonneg : 0 ≤ ∑ x : α, (f x).toReal :=
    Finset.sum_nonneg (fun x _ => ENNReal.toReal_nonneg)
  have hsumCast :
      (∑ x : α, f x) =
        ENNReal.ofReal (∑ x : α, (f x).toReal) := by
    calc
      (∑ x : α, f x) =
          ∑ x : α, ENNReal.ofReal ((f x).toReal) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (ENNReal.ofReal_toReal (htermNotTop x)).symm
      _ = ENNReal.ofReal (∑ x : α, (f x).toReal) :=
        (ENNReal.ofReal_sum_of_nonneg
          (fun x _ => ENNReal.toReal_nonneg)).symm
  have hcast :
      ENNReal.ofReal
          ((∑ x : α, (f x).toReal) / (Fintype.card α : ℝ)) =
        ENNReal.ofReal R := by
    calc
      ENNReal.ofReal
          ((∑ x : α, (f x).toReal) / (Fintype.card α : ℝ)) =
          ENNReal.ofReal (∑ x : α, (f x).toReal) *
            ENNReal.ofReal ((Fintype.card α : ℝ)⁻¹) := by
        rw [div_eq_mul_inv]
        exact ENNReal.ofReal_mul hsumNonneg
      _ = ((Fintype.card α : ENNReal)⁻¹) *
            (∑ x : α, f x) := by
        rw [ENNReal.ofReal_inv_of_pos hcardReal, ← hsumCast, mul_comm]
        simp
      _ = ENNReal.ofReal R := havg
  have haverageNonneg :
      0 ≤ (∑ x : α, (f x).toReal) / (Fintype.card α : ℝ) :=
    div_nonneg hsumNonneg hcardReal.le
  have ht := congrArg ENNReal.toReal hcast
  simpa only [ENNReal.toReal_ofReal haverageNonneg,
    ENNReal.toReal_ofReal hR] using ht

/-- The Boolean cube has precisely `2^n` possible initial search points.
This identity prevents any hidden change of normalization in the switch
from finite uniform averages to the sample-path law. -/
private theorem stage169_card_bitString (n : ℕ) :
    Fintype.card (BitString n) = 2 ^ n := by
  classical
  simp [BitString]


/-- Non-vacuity witness: `p = 1/2`, dimension one and target score
one satisfy all proposed admissibility assumptions. -/
example : (0 : ℝ) < (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) < 1 ∧ (1 : ℕ) ≤ 1 := by
  norm_num

/-- Proposed exact uniform-start expected time to reach an intermediate
LeadingOnes target. Each level below the target contributes its visited-level
probability `1/2` times its exact mean residence time. -/
theorem proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hk : k ≤ n) :
    leadingOnesUniformFixedTargetMean n p k =
      (1 / 2 : ℝ) *
        (Finset.range k).sum (fun i =>
          (p * (1 - p) ^ i)⁻¹) := by
  classical
  -- The finite Boolean-cube trajectory uses the canonical measurable
  -- product structure. Neither the Bellman runtime nor the real average
  -- depends on an arbitrary replacement of that structure.
  let R : ℝ :=
    (1 / 2 : ℝ) *
      (Finset.range k).sum (fun i => (p * (1 - p) ^ i)⁻¹)
  have hfactor : 0 ≤ 1 - p := by linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro i _
    exact inv_nonneg.mpr (mul_nonneg hp0.le (pow_nonneg hfactor i))
  let f : BitString n → ENNReal := fun x =>
    runtimeSup
      (onePlusOneTransition p (leadingOnesReal (n := n)))
      (leadingOnesAtLeast (n := n) k) x
  have hENN :
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, f x) = ENNReal.ofReal R := by
    calc
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ x : BitString n, f x) =
        leadingOnesUniformFixedTargetENNMean n p hp0.le hp1.le k := by
        exact (leadingOnesUniformFixedTargetENNMean_eq_runtimeSup_average
          p hp0.le hp1.le k).symm
      _ = ENNReal.ofReal R :=
        leadingOnesUniformFixedTargetENNMean_eq_formula hp0 hp1 k hk
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  have hreal := stage169_finite_uniform_ennreal_average_toReal
    f R hR hENN
  unfold leadingOnesUniformFixedTargetMean
  change (∑ x : BitString n, (f x).toReal) / (2 : ℝ) ^ n = R
  have hcardR : (Fintype.card (BitString n) : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast stage169_card_bitString n
  rw [← hcardR]
  exact hreal

end ECRuntime
