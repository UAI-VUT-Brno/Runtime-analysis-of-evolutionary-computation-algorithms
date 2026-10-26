import ECRuntime.LeadingOnesFirstCrossingAggregate
import ECRuntime.FitnessLevel
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 7: eventual crossing of a LeadingOnes boundary

Stage 27 fix 6 compiler-verifies equality of the aggregate exact-entry and strict-skip
masses after summing over every finite first-crossing time.  The remaining normalization
question is whether the process crosses a fixed nonterminal boundary almost surely.

This file proves that eventual-crossing statement for the standard mutation regime
`0 < p < 1`.  The proof deliberately reuses the finite-state runtime infrastructure
already present in the repository.

For a boundary coordinate `i`, define the truncated distance

  `i.val - leadingOnes x`.

Elitist selection never increases this potential.  If its value is positive, the
current exact LeadingOnes level is some `j < i`; the canonical exit-mask family from
`LeadingOnesExit.lean` has total mutation weight `p * (1-p)^j` and strictly decreases
this boundary potential.  A uniform harmonic fitness-level rate is obtained from the
smaller quantity

  `p * (1-p)^i / (i+1)`.

Hence the unrestricted expected hitting time of the boundary target is finite.  The
verified equality between `runtimeSup` and the lower integral of the conventional
sample-path first-hitting time then implies that the hitting time is finite almost
surely.  Averaging over the uniform initial state gives total eventual-crossing mass one.

The next slice only needs to identify the Stage-27 aggregate first-crossing mass with
this normalized uniform eventual-crossing mass.  Combined with the fix-6 exact/skip
symmetry, that will yield the classical visit probability `1/2`.
-/

/-- Distance still remaining before the LeadingOnes value reaches boundary `i`. -/
def leadingOnesBoundaryPotential {n : ℕ} (i : Fin n) (x : BitString n) : ℕ :=
  i.val - leadingOnes x

/-- Search points which have reached or crossed boundary `i`. -/
def leadingOnesBoundaryTarget {n : ℕ} (i : Fin n) : Set (BitString n) :=
  {x | i.val ≤ leadingOnes x}

/-- The zero set of the boundary potential is exactly the boundary target. -/
theorem potentialTarget_leadingOnesBoundaryPotential
    {n : ℕ} (i : Fin n) :
    potentialTarget (leadingOnesBoundaryPotential i) = leadingOnesBoundaryTarget i := by
  ext x
  change (i.val - leadingOnes x = 0) ↔ i.val ≤ leadingOnes x
  omega

/-- Elitist LeadingOnes selection never increases the distance to a fixed boundary. -/
theorem leadingOnesBoundaryPotential_selectedAfterMask_le
    {n : ℕ} (i : Fin n) (x : BitString n) (mask : MutationMask n) :
    leadingOnesBoundaryPotential i
        (selectedAfterMask (leadingOnesReal (n := n)) x mask) ≤
      leadingOnesBoundaryPotential i x := by
  have hmono := leadingOnes_selectedAfterMask_mono x mask
  unfold leadingOnesBoundaryPotential
  omega

/-- Finite family of all canonical masks leaving an exact LeadingOnes level. -/
noncomputable def leadingOnesExitMaskFamily {n : ℕ} (j : Fin n) :
    Finset (MutationMask n) := by
  classical
  exact Finset.univ.image (leadingOnesExitMask j)

/-- Summing the mutation weights over the canonical full-mask family recovers the
verified suffix-parameterized exit probability. -/
theorem leadingOnesExitMaskFamily_weight_eq
    {n : ℕ} (p : ℝ) (j : Fin n) :
    (∑ mask ∈ leadingOnesExitMaskFamily j, mutationMaskWeight p mask) =
      p * (1 - p) ^ j.val := by
  classical
  unfold leadingOnesExitMaskFamily
  rw [Finset.sum_image]
  · simpa using leadingOnesExitMaskFamilyWeight_eq p j
  · intro a _ha b _hb hab
    exact leadingOnesExitMask_injective j hab

/-- Every canonical exit mask is accepted and strictly raises the current exact
LeadingOnes level. -/
theorem leadingOnes_selectedAfterExitMask_gt
    {n : ℕ} (x : BitString n) (j : Fin n)
    (hlevel : leadingOnes x = j.val)
    (suffix : MutationMask (n - (j.val + 1))) :
    j.val < leadingOnes
      (selectedAfterMask (leadingOnesReal (n := n)) x
        (leadingOnesExitMask j suffix)) := by
  have hmut := leadingOnes_exitMask_causes_exit x j hlevel suffix
  have haccNat :
      leadingOnes x ≤ leadingOnes (mutateWithMask x (leadingOnesExitMask j suffix)) := by
    rw [hlevel]
    exact Nat.le_of_lt hmut
  have haccReal :
      leadingOnesReal x ≤
        leadingOnesReal (mutateWithMask x (leadingOnesExitMask j suffix)) := by
    unfold leadingOnesReal
    exact_mod_cast haccNat
  unfold selectedAfterMask elitistSelect
  rw [if_pos haccReal]
  exact hmut

/-- At an exact level `j < i`, every canonical exit mask strictly decreases the
boundary potential. -/
theorem leadingOnesExitMaskFamily_progress_subset
    {n : ℕ} (i j : Fin n) (x : BitString n)
    (hlevel : leadingOnes x = j.val) (hji : j.val < i.val) :
    ∀ mask ∈ leadingOnesExitMaskFamily j,
      leadingOnesBoundaryPotential i
          (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
        leadingOnesBoundaryPotential i x := by
  classical
  intro mask hmask
  unfold leadingOnesExitMaskFamily at hmask
  rw [Finset.mem_image] at hmask
  rcases hmask with ⟨suffix, _hsuffix, rfl⟩
  have hraise := leadingOnes_selectedAfterExitMask_gt x j hlevel suffix
  unfold leadingOnesBoundaryPotential
  rw [hlevel]
  omega

/-- Exact current-level exit probability is a lower bound on one-step strict progress of
`leadingOnesBoundaryPotential`. -/
theorem leadingOnesBoundaryPotential_progressMass_lower
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n)
    (hx : 0 < leadingOnesBoundaryPotential i x) :
    p * (1 - p) ^ (leadingOnes x) ≤
      finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          leadingOnesBoundaryPotential i
              (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
            leadingOnesBoundaryPotential i x) := by
  classical
  have hbelow : leadingOnes x < i.val := by
    simpa [leadingOnesBoundaryPotential] using hx
  let j : Fin n := ⟨leadingOnes x, lt_trans hbelow i.isLt⟩
  have hlevel : leadingOnes x = j.val := by rfl
  have hsub : ∀ mask ∈ leadingOnesExitMaskFamily j,
      leadingOnesBoundaryPotential i
          (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
        leadingOnesBoundaryPotential i x :=
    leadingOnesExitMaskFamily_progress_subset i j x hlevel hbelow
  calc
    p * (1 - p) ^ (leadingOnes x) =
        ∑ mask ∈ leadingOnesExitMaskFamily j, mutationMaskWeight p mask := by
      rw [leadingOnesExitMaskFamily_weight_eq]
    _ ≤ finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          leadingOnesBoundaryPotential i
              (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
            leadingOnesBoundaryPotential i x) := by
      exact sum_le_finiteEventMass_of_subset
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          leadingOnesBoundaryPotential i
              (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
            leadingOnesBoundaryPotential i x)
        (leadingOnesExitMaskFamily j)
        (fun mask => mutationMaskWeight_nonneg hp0 hp1 mask)
        hsub

/-- Powers of a real number in `[0,1]` decrease as the natural exponent increases. -/
theorem pow_antitone_nat_of_mem_unitInterval
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ {a b : ℕ}, a ≤ b → q ^ b ≤ q ^ a := by
  intro a b hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  rw [pow_add]
  have hpowOne : q ^ d ≤ 1 := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [pow_succ]
        calc
          q ^ d * q ≤ 1 * q := mul_le_mul_of_nonneg_right ih hq0
          _ ≤ 1 := by simpa using hq1
  calc
    q ^ a * q ^ d ≤ q ^ a * 1 :=
      mul_le_mul_of_nonneg_left hpowOne (pow_nonneg hq0 a)
    _ = q ^ a := by ring

/-- Uniform harmonic-fitness-level rate used to reach boundary `i`. -/
noncomputable def leadingOnesBoundaryProgressRate {n : ℕ} (p : ℝ) (i : Fin n) : ℝ :=
  p * (1 - p) ^ i.val / ((i.val + 1 : ℕ) : ℝ)

/-- The boundary rate is strictly positive in the standard nondegenerate mutation
regime `0 < p < 1`. -/
theorem leadingOnesBoundaryProgressRate_pos
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    0 < leadingOnesBoundaryProgressRate p i := by
  unfold leadingOnesBoundaryProgressRate
  have hq : 0 < 1 - p := by linarith
  positivity

/-- The rate above satisfies the progress hypothesis of the generic harmonic
fitness-level theorem. -/
theorem leadingOnesBoundaryPotential_hasProgress
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (i : Fin n) (x : BitString n)
    (hx : 0 < leadingOnesBoundaryPotential i x) :
    (leadingOnesBoundaryPotential i x : ℝ) *
        leadingOnesBoundaryProgressRate p i ≤
      finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          leadingOnesBoundaryPotential i
              (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
            leadingOnesBoundaryPotential i x) := by
  have hbelow : leadingOnes x < i.val := by
    simpa [leadingOnesBoundaryPotential] using hx
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ i.val ≤ (1 - p) ^ (leadingOnes x) :=
    pow_antitone_nat_of_mem_unitInterval hq0 hq1 (Nat.le_of_lt hbelow)
  have hVle : leadingOnesBoundaryPotential i x ≤ i.val + 1 := by
    unfold leadingOnesBoundaryPotential
    omega
  have hVcast :
      (leadingOnesBoundaryPotential i x : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hVle
  have hden : 0 < ((i.val + 1 : ℕ) : ℝ) := by positivity
  have hfrac :
      (leadingOnesBoundaryPotential i x : ℝ) / ((i.val + 1 : ℕ) : ℝ) ≤ 1 := by
    exact (div_le_one hden).2 hVcast
  have hbase : 0 ≤ p * (1 - p) ^ i.val :=
    mul_nonneg hp0.le (pow_nonneg hq0 _)
  have hrateBound :
      (leadingOnesBoundaryPotential i x : ℝ) *
          leadingOnesBoundaryProgressRate p i ≤
        p * (1 - p) ^ (leadingOnes x) := by
    calc
      (leadingOnesBoundaryPotential i x : ℝ) *
          leadingOnesBoundaryProgressRate p i =
          (p * (1 - p) ^ i.val) *
            ((leadingOnesBoundaryPotential i x : ℝ) /
              ((i.val + 1 : ℕ) : ℝ)) := by
        unfold leadingOnesBoundaryProgressRate
        ring
      _ ≤ (p * (1 - p) ^ i.val) * 1 :=
        mul_le_mul_of_nonneg_left hfrac hbase
      _ = p * (1 - p) ^ i.val := by ring
      _ ≤ p * (1 - p) ^ (leadingOnes x) :=
        mul_le_mul_of_nonneg_left hpow hp0.le
  exact hrateBound.trans
    (leadingOnesBoundaryPotential_progressMass_lower hp0.le hp1.le i x hx)

/-- The generic harmonic fitness-level theorem gives a finite-horizon runtime bound for
reaching a fixed LeadingOnes boundary. -/
theorem leadingOnesBoundary_hasUniformFiniteHorizonRuntimeBound
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    HasUniformFiniteHorizonRuntimeBound
      (onePlusOneTransition p (leadingOnesReal (n := n)))
      (potentialTarget (leadingOnesBoundaryPotential i))
      (harmonicLevelRuntime
        (leadingOnesBoundaryProgressRate p i)
        (leadingOnesBoundaryPotential i)) := by
  have hgeneric := harmonicFitnessLevel_finiteHorizonBound
    (w := fun (_x : BitString n) (mask : MutationMask n) => mutationMaskWeight p mask)
    (step := selectedAfterMask (leadingOnesReal (n := n)))
    (V := leadingOnesBoundaryPotential i)
    (rate := leadingOnesBoundaryProgressRate p i)
    (hrate := leadingOnesBoundaryProgressRate_pos hp0 hp1 i)
    (hw := fun _x mask => mutationMaskWeight_nonneg hp0.le hp1.le mask)
    (hsum := fun _x => mutationMaskWeight_sum n p)
    (hmono := fun x mask => leadingOnesBoundaryPotential_selectedAfterMask_le i x mask)
    (hprogress := fun x hx => leadingOnesBoundaryPotential_hasProgress hp0 hp1 i x hx)
  simpa [onePlusOneTransition_eq_finiteRandomTransition] using hgeneric

/-- The unrestricted expected time to a fixed boundary is finite. -/
theorem leadingOnesBoundary_runtimeSup_ne_top
    {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (i : Fin n) (x : BitString n) :
    runtimeSup
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (potentialTarget (leadingOnesBoundaryPotential i)) x ≠ ⊤ := by
  have hB := leadingOnesBoundary_hasUniformFiniteHorizonRuntimeBound hp0 hp1 i
  have hle := runtimeSup_le_of_uniform_bound
    (onePlusOneTransition p (leadingOnesReal (n := n)))
    (potentialTarget (leadingOnesBoundaryPotential i))
    (harmonicLevelRuntime
      (leadingOnesBoundaryProgressRate p i)
      (leadingOnesBoundaryPotential i))
    hB x
  exact ne_top_of_le_ne_top (by simp) hle

/-- A conventional first-hitting time is finite exactly when the target is reached at
some natural time. -/
theorem transitionTrajectoryFirstHittingTime_lt_top_iff_exists_hit
    {α : Type*} (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (x : α) (path : ℕ → α) :
    transitionTrajectoryFirstHittingTime target x path < ⊤ ↔
      ∃ t : ℕ, transitionTrajectoryState x path t ∈ target := by
  classical
  unfold transitionTrajectoryFirstHittingTime
  by_cases h : ∃ t : ℕ, transitionTrajectoryState x path t ∈ target
  · rw [dif_pos h]
    constructor
    · intro _
      exact h
    · intro _
      simp
  · rw [dif_neg h]
    simp [h]

/-- Infinite-path event that the run eventually reaches or crosses boundary `i`. -/
def leadingOnesEventuallyCrossesBoundarySet
    {n : ℕ} (i : Fin n) (x : BitString n) : Set (ℕ → BitString n) :=
  {path |
    transitionTrajectoryFirstHittingTime
      (potentialTarget (leadingOnesBoundaryPotential i)) x path < ⊤}

/-- Semantic characterization of the eventual-boundary-crossing event. -/
theorem mem_leadingOnesEventuallyCrossesBoundarySet_iff
    {n : ℕ} (i : Fin n) (x : BitString n) (path : ℕ → BitString n) :
    path ∈ leadingOnesEventuallyCrossesBoundarySet i x ↔
      ∃ t : ℕ, i.val ≤ leadingOnes (transitionTrajectoryState x path t) := by
  change
    transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesBoundaryPotential i)) x path < ⊤ ↔
      ∃ t : ℕ, i.val ≤ leadingOnes (transitionTrajectoryState x path t)
  rw [transitionTrajectoryFirstHittingTime_lt_top_iff_exists_hit]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change leadingOnesBoundaryPotential i
        (transitionTrajectoryState x path t) = 0 at ht
    unfold leadingOnesBoundaryPotential at ht
    omega
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    change leadingOnesBoundaryPotential i
        (transitionTrajectoryState x path t) = 0
    unfold leadingOnesBoundaryPotential
    omega

/-- Eventual boundary crossing is a measurable trajectory event. -/
theorem measurableSet_leadingOnesEventuallyCrossesBoundarySet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (i : Fin n) (x : BitString n) :
    MeasurableSet (leadingOnesEventuallyCrossesBoundarySet i x) := by
  change MeasurableSet
    ((transitionTrajectoryFirstHittingTime
      (potentialTarget (leadingOnesBoundaryPotential i)) x) ⁻¹' Set.Iio ⊤)
  exact measurableSet_Iio.preimage
    (measurable_transitionTrajectoryFirstHittingTime
      (potentialTarget (leadingOnesBoundaryPotential i)) x)

/-- Under `0 < p < 1`, every fixed-initial-state LeadingOnes run eventually crosses
boundary `i` with probability one. -/
theorem transitionTrajectoryMeasure_leadingOnesEventuallyCrossesBoundarySet
    {n : ℕ} {p : ℝ}
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (hp0 : 0 < p) (hp1 : p < 1)
    (i : Fin n) (x : BitString n) :
    transitionTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0.le hp1.le
          (leadingOnesReal (n := n))) x
        (leadingOnesEventuallyCrossesBoundarySet i x) = 1 := by
  let P := onePlusOneTransition p (leadingOnesReal (n := n))
  have hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0.le hp1.le (leadingOnesReal (n := n))
  have hrun :
      runtimeSup P (potentialTarget (leadingOnesBoundaryPotential i)) x ≠ ⊤ := by
    simpa [P] using leadingOnesBoundary_runtimeSup_ne_top hp0 hp1 i x
  have hlintegral :
      (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime
          (potentialTarget (leadingOnesBoundaryPotential i)) x path
        ∂transitionTrajectoryMeasure P hP x) ≠ ⊤ := by
    rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
      P (potentialTarget (leadingOnesBoundaryPotential i)) hP x]
    exact hrun
  have hae : ∀ᵐ path ∂transitionTrajectoryMeasure P hP x,
      transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesBoundaryPotential i)) x path < ⊤ := by
    exact ae_lt_top
      (measurable_transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesBoundaryPotential i)) x)
      hlintegral
  rw [ae_iff] at hae
  have hcomp :
      transitionTrajectoryMeasure P hP x
        (leadingOnesEventuallyCrossesBoundarySet i x)ᶜ = 0 := by
    have hset :
        (leadingOnesEventuallyCrossesBoundarySet i x)ᶜ =
          {path |
            transitionTrajectoryFirstHittingTime
              (potentialTarget (leadingOnesBoundaryPotential i)) x path = ⊤} := by
      ext path
      simp [leadingOnesEventuallyCrossesBoundarySet, lt_top_iff_ne_top]
    rw [hset]
    simpa only [not_lt, top_le_iff] using hae
  have hmeas := measurableSet_leadingOnesEventuallyCrossesBoundarySet i x
  have hsum := measure_add_measure_compl
    (μ := transitionTrajectoryMeasure P hP x) hmeas
  rw [hcomp] at hsum
  simpa using hsum

/-- Uniform-initialization mass of eventual crossing of boundary `i`. -/
noncomputable def leadingOnesUniformEventualCrossingMass
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin n) : ENNReal :=
  ((Fintype.card (BitString n) : ENNReal)⁻¹) *
    ∑ x : BitString n,
      transitionTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1
          (leadingOnesReal (n := n))) x
        (leadingOnesEventuallyCrossesBoundarySet i x)

/-- The uniform eventual-crossing mass is one in the nondegenerate mutation regime. -/
theorem leadingOnesUniformEventualCrossingMass_eq_one
    {n : ℕ} {p : ℝ}
    [MeasurableSpace (BitString n)] [MeasurableSingletonClass (BitString n)]
    (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesUniformEventualCrossingMass p hp0.le hp1.le i = 1 := by
  unfold leadingOnesUniformEventualCrossingMass
  simp_rw [transitionTrajectoryMeasure_leadingOnesEventuallyCrossesBoundarySet hp0 hp1 i]
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  have hcard : Fintype.card (BitString n) ≠ 0 := Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul, mul_one]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast hcard
  · exact ENNReal.natCast_ne_top _

end ECRuntime
