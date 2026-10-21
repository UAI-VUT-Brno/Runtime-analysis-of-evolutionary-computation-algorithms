import ECRuntime.LeadingOnesMainResults
import ECRuntime.WittMutationLogThreeRuntime
import ECRuntime.StaticUnaryUnbiasedPivotDrift
import ECRuntime.StaticUnaryUnbiasedPivotPartition
import ECRuntime.StaticUnaryUnbiasedGlobalDrift
import ECRuntime.StaticUnaryUnbiasedCorrectedRuntime
import ECRuntime.StaticUnaryUnbiasedExplicitRuntime
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.StaticUnaryUnbiasedSharpMomentUpper
import ECRuntime.StaticUnaryUnbiasedRadiusTruncation
import ECRuntime.StaticUnaryUnbiasedAcceptedRadiusTail
import ECRuntime.StaticUnaryUnbiasedAcceptedTailLoss
import ECRuntime.StaticUnaryUnbiasedCoordinateTailLoss
import ECRuntime.StaticUnaryUnbiasedTailCoordinateMoment
import ECRuntime.StaticUnaryUnbiasedShortRadiusPivot

open ECRuntime

/-!
# Non-vacuity witnesses

A theorem with unsatisfiable hypotheses is vacuously true and says nothing. Every
facade result below is therefore instantiated at a concrete point that discharges
*all* of its hypotheses simultaneously, including the instance arguments.

These examples deliberately avoid forcing the concrete statements to reduce:
instantiating, say, `leadingOnesUniformFirstHittingTimeExpectation 4` as an equation
makes the elaborator evaluate `Fintype.card (BitString 4)` and the whole sum, which
times out and tests nothing useful. Applying the theorem is what establishes that the
hypothesis set is inhabited.
-/

namespace ECRuntimeTest

/-- The Witt log-three interval is non-degenerate: it contains the standard scale `c = 1`.

This is the arithmetic content of `c ≤ log 3` being a genuine constraint rather than an
empty one, and it is what lets the witness below use `c = 1`. -/
theorem one_le_logThreeScale : (1 : ℝ) ≤ wittMutationC3LogThreeScale := by
  rw [wittMutationC3LogThreeScale_eq, Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  linarith

/-- The log-three scale is strictly positive, so `0 < c ≤ log 3` is a non-empty range. -/
theorem logThreeScale_pos : 0 < wittMutationC3LogThreeScale :=
  lt_of_lt_of_le zero_lt_one one_le_logThreeScale

/-- The LeadingOnes hypothesis set is satisfiable.

The measurability instances are inhabited (the discrete `⊤` structure works, and makes
every singleton measurable), and `p = 1/2` satisfies `0 < p < 1`. -/
example : True := by
  letI : MeasurableSpace (BitString 4) := ⊤
  haveI : MeasurableSingletonClass (BitString 4) := ⟨fun _ => trivial⟩
  have _witness := leadingOnesUniformFirstHittingTimeExpectation_eq_formula
    (n := 4) (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  trivial

/-- The Witt log-three runtime hypothesis set is satisfiable.

`n = 4` meets `4 ≤ n`; `c = 1` meets `0 < c ≤ log 3` by `one_le_logThreeScale`; and the
constant weight vector `w ≡ 1` is both positive and nonincreasing. -/
example : True := by
  have _witness := wittMutation_runtimeSup_le_logThreeScale_log_bound
    (n := 4) (by norm_num) (c := 1) (by norm_num) one_le_logThreeScale
    (fun _ => (1 : ℝ)) (fun _ => by norm_num) (fun _ _ _ => le_refl _) (allZeros 4)
  trivial

/-- The same witness discharges the exact-rate envelope on the log-three interval. -/
example : True := by
  have _witness := wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale
    (n := 4) (by norm_num) (c := 1) (by norm_num) one_le_logThreeScale
    (fun _ => (1 : ℝ)) (fun _ => by norm_num) (fun _ _ _ => le_refl _) (allZeros 4)
  trivial


/-- The Stage-80 corrected unconditioning and final sign-bound hypotheses are
simultaneously satisfiable on a nonempty, positive-probability pivot event.

Take two coordinates, independent bit mutation with `p = 1/2`, positive constant
objective weights, the all-zero point, and `alpha = 2`.  The singleton at pivot
zero has strictly positive mass, so this also exercises the positive-mass
conditional-loss theorem (not merely its zero-event branch).
The same event witnesses all three Stage-81 interfaces at alpha = 2,
the Stage-82 unique-pivot/exact-partition interfaces, Stage-83 global drift,
the Stage-84 runtime certificate, and the Stage-85 explicit runtime envelope.
The empty
mask witnesses the no-improving-flip hypothesis with signed coefficients. -/
example : True := by
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : ℝ)
      (by norm_num) (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let x : BitString 2 := allZeros 2
  let i : Fin 2 := 0
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hmono : NonincreasingLinearWeights w := by
    intro _ _ _
    simp [w]
  have hi : x i = false := by
    rfl
  have hp1 : 0 < law.oneBitMass := by
    change 0 < (StaticUnaryUnbiasedMutation.independentBitLaw (n := 2)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)).oneBitMass
    rw [StaticUnaryUnbiasedMutation.independentBitLaw_oneBitMass]
    norm_num
  have hsingle : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i :=
    StaticUnaryUnbiasedMutation.singleton_mem_acceptedLeftmostZeroEvent
      w hw x i hi
  have hweight : 0 < law.weight ({i} : MutationMask 2) := by
    rw [law.singletonWeight_eq_oneBitMass_div (by norm_num) i]
    exact div_pos hp1 (by norm_num)
  have hevent : 0 < law.maskEventMass
      (StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i) :=
    lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i) i hsingle)
  have _conditionalWitness := law.acceptedRightConditionalLossProxy_eq_div_of_mass_pos
    (StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i)
    hevent (fun _ => (1 : ℝ)) x i
  have _boundWitness :=
    law.acceptedLeftmostZeroEvent_correctedRightWeightedLoss_le_singletonRate_weight_div
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x i hi
  have _signWitness :=
    law.neg_singletonRate_correctedWeight_div_le_acceptedRightWeightedContribution
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x i hi
  -- Stage 81: the identity, corrected restricted drift and its nonnegativity
  -- all admit these exact concrete parameters with strictly positive event mass.
  have _decompositionWitness :=
    law.acceptedLeftmostZeroEvent_weightedPotentialDrop_eq_left_add_right
      w (law.correctedPotentialWeight (2 : ℝ) w) x i i
  have _restrictedDriftWitness :=
    law.acceptedLeftmostZeroEvent_correctedWeightedPotentialDrop_lower_bound
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x i hi
  have _nonnegativeDriftWitness :=
    law.acceptedLeftmostZeroEvent_correctedWeightedPotentialDrop_nonneg
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x i hi
  -- Stage 82: the singleton accepted pivot is a genuine improving event.
  -- The zero-flip branch is populated by the empty mask, and the two
  -- remaining identities can be instantiated even with signed g.
  have haccepted : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask 2)) :=
    StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_accepts
      w x i ({i} : MutationMask 2) hsingle
  have himproving : (zeroToOneFlips x ({i} : MutationMask 2)).Nonempty := by
    refine ⟨i, ?_⟩
    exact ((StaticUnaryUnbiasedMutation.mem_acceptedLeftmostZeroEvent_iff
      w x i ({i} : MutationMask 2)).1 hsingle).1
  have _uniquePivotWitness :=
    StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_existsUnique_of_accepts
      w x ({i} : MutationMask 2) haccepted himproving
  have hnone : zeroToOneFlips x (∅ : MutationMask 2) = ∅ := by
    simp [zeroToOneFlips]
  have _noFlipWitness :=
    StaticUnaryUnbiasedMutation.linearErrorPotential_selected_drop_eq_zero_of_noZeroToOneFlips
      w (fun _ : Fin 2 => (-1 : ℝ)) hw x (∅ : MutationMask 2) hnone
  have _indicatorWitness :=
    StaticUnaryUnbiasedMutation.sum_zeroPositions_acceptedLeftmostZeroEvent_indicator
      w x ({i} : MutationMask 2) (1 : ℝ)
  have _globalSignedWitness :=
    law.acceptedEventWeightedPotentialDrop_univ_eq_sum_pivots
      w (fun _ : Fin 2 => (-1 : ℝ)) hw x
  -- Stage 83: the same concrete positive-mass law witnesses the unrestricted
  -- corrected lower bound, the exact drift bridge, and multiplicative drift.
  have _globalMaskBoundWitness :=
    law.acceptedEventWeightedPotentialDrop_univ_corrected_lower_bound
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x
  have _kernelBridgeWitness :=
    law.correctedLinearPotential_drift_eq_acceptedEventWeightedPotentialDrop_univ
      (2 : ℝ) w x
  have _globalDriftWitness :=
    law.correctedLinearPotential_global_multiplicative_drift_lower_bound
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x
  -- Stage 84: the positive rate, named multiplicative-drift certificate,
  -- and unrestricted hitting-time estimate all admit these same concrete
  -- parameters; x = allZeros 2 is genuinely nonoptimal.
  have _rateWitness :=
    law.correctedLinearPotential_multiplicativeRate_pos
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
  have _multiplicativeWitness :=
    law.correctedLinearPotential_hasMultiplicativeDriftLowerBound
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono
  have _runtimeWitness :=
    law.correctedLinearPotential_runtimeSup_le
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x
  -- Stage 85: non-vacuous geometric envelopes and explicit expected runtime
  -- for the same positive-rate two-bit law. All three theorem hypotheses
  -- are simultaneously satisfiable, independently of any numerical reduction.
  have _coefficientEnvelopeWitness :=
    law.correctedPotentialWeight_le_dimension_geometric
      (by norm_num) (alpha := (2 : ℝ)) (by norm_num)
      w hw i
  have _potentialEnvelopeWitness :=
    law.correctedLinearPotential_le_dimension_geometric
      (by norm_num) (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x
  have _explicitRuntimeWitness :=
    law.correctedLinearPotential_runtimeSup_le_explicit
      (by norm_num) hp1 (alpha := (2 : ℝ)) (by norm_num)
      w hw hmono x
  trivial


/-- A concrete radius-one mutation law witnesses the Stage 86 moment-family
hypotheses and each of the seven theorem interfaces. Here `n = 2`, singleton
mass and mean radius are one, and the second factorial moment is zero.
The all-zero state is genuinely non-optimal and `w ≡ 1` is positive and
nonincreasing. Unlike independent-bit mutation, this law flips exactly one bit. -/
example : True := by
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let x : BitString 2 := allZeros 2
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hmono : NonincreasingLinearWeights w := by
    intro _ _ _
    simp [w]
  have hmass : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass (n := 2)
      (by norm_num)
  have hmean : law.meanRadius = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_meanRadius (n := 2)
      (by norm_num)
  have hsecond : law.secondFactorialRadiusMoment = 0 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_secondFactorialRadiusMoment
      (n := 2) (by norm_num)
  have hp₀ : (1 / 2 : ℝ) ≤ law.oneBitMass := by
    rw [hmass]
    norm_num
  have hmeanLe : law.meanRadius ≤ (1 : ℝ) := le_of_eq hmean
  have hsecondLe : law.secondFactorialRadiusMoment ≤ (0 : ℝ) :=
    le_of_eq hsecond
  have _uniformEnvelopeWitness :=
    law.correctedLinearPotential_runtimeSup_le_uniform_moments
      (by norm_num) (p₀ := (1 / 2 : ℝ)) (by norm_num) hp₀
      (C₁ := (1 : ℝ)) (C₂ := (0 : ℝ))
      (by norm_num) (by norm_num) hmeanLe hsecondLe
      (alpha := (2 : ℝ)) (by norm_num) w hw hmono x
  have _uniformNlognWitness :=
    law.correctedLinearPotential_runtimeSup_le_uniform_nlogn
      (by norm_num) (p₀ := (1 / 2 : ℝ)) (by norm_num) hp₀
      (C₁ := (1 : ℝ)) (C₂ := (0 : ℝ))
      (by norm_num) (by norm_num) hmeanLe hsecondLe
      (alpha := (2 : ℝ)) (by norm_num) w hw hmono x
  have _singletonMassWitness :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass (n := 2)
      (by norm_num)
  have _radiusOneWitness :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_radiusMass (n := 2)
      (by norm_num) 1
  have _meanRadiusWitness :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_meanRadius (n := 2)
      (by norm_num)
  have _factorialMomentWitness :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_secondFactorialRadiusMoment
      (n := 2) (by norm_num)
  have _oneBitRuntimeWitness :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_runtimeSup_le
      (n := 2) (by norm_num) w hw hmono x
  trivial

/-- The seven Stage 87 interfaces have simultaneously satisfiable assumptions.
The sharp eventual estimates are applied at a dimension beyond both compiler-
proved thresholds using a genuinely normalized uniform one-bit mutation law.
Thus the existential quantifier in the theorem is not witnessed only formally:
for every sufficiently large dimension there is a positive-mass radius law and
an actual nonoptimal state to which the theorem applies. -/
example : True := by
  have _slackPosWitness :=
    StaticUnaryUnbiasedMutation.one_lt_correctedMomentSlack 2
  have _slackLimitWitness :=
    StaticUnaryUnbiasedMutation.correctedMomentSlack_growth
  have _rationalIdentityWitness :=
    StaticUnaryUnbiasedMutation.correctedNormalizedMomentEnvelope_eq_rational
      (D := (0 : ℝ)) (n := 2) (by norm_num)
  have _rationalLimitWitness :=
    StaticUnaryUnbiasedMutation.correctedNormalizedMomentEnvelope_tendsto_one
      (0 : ℝ)
  obtain ⟨N, hN⟩ :=
    StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le_sharpUpper_of_ratio_bound
      (D := (0 : ℝ)) (epsilon := (1 : ℝ))
      (by norm_num) (by norm_num)
  obtain ⟨N', hN'⟩ :=
    StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments
      (p₀ := (1 / 2 : ℝ)) (C₁ := (1 : ℝ)) (C₂ := (0 : ℝ))
      (epsilon := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let n : ℕ := N + N' + 2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hnN : N ≤ n := by dsimp [n]; omega
  have hnN' : N' ≤ n := by dsimp [n]; omega
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn
  let law : StaticUnaryUnbiasedMutation n :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw hnPos
  let w : Fin n → ℝ := fun _ => 1
  let x : BitString n := allZeros n
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hmono : NonincreasingLinearWeights w := by
    intro _ _ _
    simp [w]
  have hmass : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass (n := n)
      hnPos
  have hmean : law.meanRadius = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_meanRadius (n := n)
      hnPos
  have hsecond : law.secondFactorialRadiusMoment = 0 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_secondFactorialRadiusMoment
      (n := n) hnPos
  have hp1 : 0 < law.oneBitMass := by
    rw [hmass]
    norm_num
  have hp0 : (1 / 2 : ℝ) ≤ law.oneBitMass := by
    rw [hmass]
    norm_num
  have hmeanLe : law.meanRadius ≤ (1 : ℝ) := le_of_eq hmean
  have hsecondLe : law.secondFactorialRadiusMoment ≤ (0 : ℝ) :=
    le_of_eq hsecond
  have hratio :
      law.meanRadius * law.secondFactorialRadiusMoment /
          law.oneBitMass ^ 2 ≤ (0 : ℝ) := by
    simp [hsecond]
  have _momentRatioWitness :=
    law.momentRatio_le_uniform_bound
      (p₀ := (1 / 2 : ℝ)) (C₁ := (1 : ℝ)) (C₂ := (0 : ℝ))
      (by norm_num) hp0 (by norm_num) (by norm_num)
      hmeanLe hsecondLe
  have _sharpRatioWitness := hN n hnN law hp1 hratio w hw hmono x
  have _sharpUniformWitness :=
    hN' n hnN' law hp0 hmeanLe hsecondLe w hw hmono x
  trivial

/-- The Stage 88 radius-truncation interfaces apply to an actual normalized
static unary-unbiased law. With `n = 2`, uniform one-bit mutation has all its
radius mass at `k = 1`. We use cutoff `b = 1` for the positive-threshold Markov
bound and all seven theorem declarations (including both summands in the exact
factorial-moment decomposition). No second-moment bound is assumed. -/
example : True := by
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  have _singletonSupport :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_radiusMass
      (n := 2) (by norm_num) 1
  have _tailNonnegative := law.radiusTailMass_nonneg 1
  have _tailScaled := law.radiusTailMass_mul_cutoff_le_meanRadius 1
  have _tailMarkov := law.radiusTailMass_le_meanRadius_div
    (b := 1) (by norm_num)
  have _truncatedBound :=
    law.truncatedSecondFactorialRadiusMoment_le_cutoff_mul_meanRadius 1
  have _truncatedNonnegative :=
    law.truncatedSecondFactorialRadiusMoment_nonneg 1
  have _longNonnegative :=
    law.tailSecondFactorialRadiusMoment_nonneg 1
  have _exactSplit :=
    law.secondFactorialRadiusMoment_eq_truncated_add_tail 1
  trivial

/-- The Stage 89 radius/mask and signed-drift results have a genuinely
positive-mass accepted high-radius event. For `n = 2`, uniform one-bit mutation
flips each coordinate with probability `1/2`. Starting from the all-zero
string with positive constant fitness weights, each singleton is accepted.
The cutoff `b = 1` also has a nonempty short-radius mask event (the empty mask).
No second-moment premise, independent-coordinate premise, or sign restriction
on potential coefficients is used in these six theorem instances. -/
example : True := by
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let g : Fin 2 → ℝ := fun _ => -1
  let x : BitString 2 := allZeros 2
  let i : Fin 2 := 0
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hi : x i = false := by
    rfl
  have hsingle : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i :=
    StaticUnaryUnbiasedMutation.singleton_mem_acceptedLeftmostZeroEvent
      w hw x i hi
  have haccept : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask 2)) :=
    StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_accepts
      w x i ({i} : MutationMask 2) hsingle
  have hhigh : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1 := by
    simp [StaticUnaryUnbiasedMutation.highRadiusMaskEvent]
  have hacceptedHigh : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1 := by
    classical
    change ({i} : MutationMask 2) ∈
      (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1).filter
        (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask))
    exact Finset.mem_filter.mpr ⟨hhigh, haccept⟩
  have hmassOne : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass (n := 2)
      (by norm_num)
  have hweight : 0 < law.weight ({i} : MutationMask 2) := by
    rw [law.singletonWeight_eq_oneBitMass_div (by norm_num) i, hmassOne]
    norm_num
  have _positiveEvent : 0 < law.maskEventMass
      (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1) :=
    lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1)
        i hacceptedHigh)
  have _shortEvent : (∅ : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) 1 := by
    simp [StaticUnaryUnbiasedMutation.shortRadiusMaskEvent]
  have _radiusIdentity :=
    law.maskEventMass_highRadiusMaskEvent_eq_radiusTailMass 1
  have _acceptedSubset :=
    StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent_subset_highRadiusMaskEvent
      w x 1
  have _acceptedMassBound :=
    law.acceptedHighRadiusMaskEvent_mass_le_meanRadius_div
      w x (b := 1) (by norm_num)
  have _signedMaskPartition :=
    StaticUnaryUnbiasedMutation.sum_mask_eq_shortRadius_add_highRadius
      (n := 2) 1 (fun mask => if mask = (∅ : MutationMask 2)
        then (1 : ℝ) else -1)
  have _signedDriftPartition :=
    law.acceptedEventWeightedPotentialDrop_univ_eq_shortRadius_add_highRadius
      w g x 1
  have _rejectedTailZero :=
    law.acceptedEventWeightedPotentialDrop_highRadius_eq_acceptedHighRadius
      w g x 1
  trivial


/-- Stage 90's eight focused-verified results have simultaneously inhabited
hypotheses for an actual normalized unary-unbiased law. At `n = 2` the
uniform-one-bit operator selects the singleton `{i}` with positive mass.
For the all-zero parent and positive linear weights, that singleton is accepted,
so the event in the exact L/R identity and the long-radius event (`b = 1`) are
not empty or probability-zero. Nonnegative error coefficients satisfy the
signed-loss and coarse first-moment bounds without any second-moment premise.
The proof below instantiates every new theorem instead of proving `True` from
a potentially vacuous antecedent. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 -> ℝ := fun _ => 1
  let g : Fin 2 -> ℝ := fun _ => 1
  let x : BitString 2 := allZeros 2
  let i : Fin 2 := 0
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hg : ∀ j : Fin 2, 0 ≤ g j := by
    intro j
    norm_num [g]
  have hi : x i = false := by rfl
  have hsingle : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i :=
    StaticUnaryUnbiasedMutation.singleton_mem_acceptedLeftmostZeroEvent
      w hw x i hi
  have haccept : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask 2)) :=
    StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_accepts
      w x i ({i} : MutationMask 2) hsingle
  let event : Finset (MutationMask 2) := {({i} : MutationMask 2)}
  have hevent : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask) := by
    intro mask hm
    have heq : mask = ({i} : MutationMask 2) := by
      simpa only [event, Finset.mem_singleton] using hm
    rw [heq]
    exact haccept
  have hhigh : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1 := by
    simp [StaticUnaryUnbiasedMutation.highRadiusMaskEvent]
  have hacceptedHigh : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1 := by
    change ({i} : MutationMask 2) ∈
      (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1).filter
        (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask))
    exact Finset.mem_filter.mpr ⟨hhigh, haccept⟩
  have hmass : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass (n := 2)
      (by norm_num)
  have hweight : 0 < law.weight ({i} : MutationMask 2) := by
    rw [law.singletonWeight_eq_oneBitMass_div (by norm_num) i, hmass]
    norm_num
  have _nonzeroAcceptedTail : 0 < law.maskEventMass
      (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1) :=
    lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1)
        i hacceptedHigh)
  have _exactEventLR :=
    law.acceptedEventWeightedPotentialDrop_eq_leftDelta_add_rightDelta_of_accepts
      w g x i event hevent
  have _exactHighLR :=
    law.acceptedHighRadiusPotentialDrop_eq_leftDelta_add_rightDelta
      w g x i 1
  have _pointwiseLoss :=
    StaticUnaryUnbiasedMutation.linearErrorPotential_selected_drop_ge_neg_oneToZeroLoss_of_accepts
      w g x ({i} : MutationMask 2) hg haccept
  have _eventLoss :=
    law.acceptedHighRadiusPotentialDrop_ge_neg_flippedOneLoss w g x 1 hg
  have _potentialBound :=
    StaticUnaryUnbiasedMutation.linearErrorPotential_le_sum_coefficients
      g hg x
  have _tailBound :=
    law.acceptedHighRadiusPotentialDrop_ge_neg_firstMomentEnvelope
      w g x hg (b := 1) (by norm_num)
  have _shortLongBound :=
    law.acceptedEventWeightedPotentialDrop_univ_ge_short_sub_firstMomentEnvelope
      w g x hg (b := 1) (by norm_num)
  have _kernelDriftBound :=
    law.linearErrorPotential_drift_ge_short_sub_firstMomentEnvelope
      w g x hg (b := 1) (by norm_num)
  trivial


/-- Stage 91 non-vacuity: use a genuine normalized unbiased law at `n = 2`,
positive potential weights, the all-one parent (hence nonempty one-positions),
and a positive-mass singleton event that flips a currently-one coordinate.
All six Stage 91 theorem interfaces are instantiated simultaneously. This does
not assume acceptance for the arbitrary positive-loss event: the acceptance-
restricted bounds are separately instantiated with their actual acceptance
filter, preserving the distinction between them. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let g : Fin 2 → ℝ := fun _ => 1
  let x : BitString 2 := allOnes 2
  let i : Fin 2 := 0
  let event : Finset (MutationMask 2) := {({i} : MutationMask 2)}
  have hg : ∀ j : Fin 2, 0 ≤ g j := by
    intro j
    norm_num [g]
  have hOne : i ∈ StaticUnaryUnbiasedMutation.onePositions x := by
    simp [StaticUnaryUnbiasedMutation.onePositions, x, allOnes]
  have hslice : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.secondCoordinateSlice event i := by
    simp [StaticUnaryUnbiasedMutation.secondCoordinateSlice, event]
  have hmassOne : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass (n := 2)
      (by norm_num)
  have hweight : 0 < law.weight ({i} : MutationMask 2) := by
    rw [law.singletonWeight_eq_oneBitMass_div (by norm_num) i, hmassOne]
    norm_num
  have hpositiveSlice : 0 < law.maskEventMass
      (StaticUnaryUnbiasedMutation.secondCoordinateSlice event i) :=
    lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.secondCoordinateSlice event i)
        i hslice)
  have _coordinateIdentity :=
    law.acceptedEventFlippedOneLoss_eq_coordinateSlices event g x
  have _lossNonnegative :=
    law.acceptedEventFlippedOneLoss_nonneg event g x hg
  have _coordinateBound :=
    law.acceptedEventFlippedOneLoss_le_oneMass_mul_meanFlipRate event g x hg
  have _acceptedTailBound :=
    law.acceptedHighRadiusPotentialDrop_ge_neg_oneMass_mul_meanFlipRate
      w g x 1 hg
  have _shortLongBound :=
    law.acceptedEventWeightedPotentialDrop_univ_ge_short_sub_oneMass_mul_meanFlipRate
      w g x 1 hg
  have _kernelDriftBound :=
    law.linearErrorPotential_drift_ge_short_sub_oneMass_mul_meanFlipRate
      w g x 1 hg
  trivial


/-- Stage 92 non-vacuity: dimension two, uniform one-bit mutation, a mixed
state with one occupied and one unoccupied position, and positive weights.
The singleton flip at the zero position is accepted and has positive mass.
All unconditional tail-moment, exchangeability, event-slice and signed-drift
interfaces are instantiated on this *same genuine law*. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let g : Fin 2 → ℝ := fun _ => 1
  let x : BitString 2 := fun j => decide (j = (0 : Fin 2))
  let i : Fin 2 := 1
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hg : ∀ j : Fin 2, 0 ≤ g j := by
    intro j
    norm_num [g]
  have hz : x i = false := by decide
  have hone : (0 : Fin 2) ∈
      StaticUnaryUnbiasedMutation.onePositions x := by
    simp [StaticUnaryUnbiasedMutation.onePositions, x]
  have hzero : i ∈ ECRuntime.zeroPositions x :=
    (ECRuntime.mem_zeroPositions x i).2 hz
  have hsingle : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i :=
    StaticUnaryUnbiasedMutation.singleton_mem_acceptedLeftmostZeroEvent
      w hw x i hz
  have haccept : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask 2)) :=
    StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_accepts
      w x i ({i} : MutationMask 2) hsingle
  have hhigh : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1 := by
    simp [StaticUnaryUnbiasedMutation.highRadiusMaskEvent]
  have hacceptedHigh : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1 := by
    change ({i} : MutationMask 2) ∈
      (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1).filter
        (fun mask => Accepts (linearFitness w) x (mutateWithMask x mask))
    exact Finset.mem_filter.mpr ⟨hhigh, haccept⟩
  have hmassOne : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass
      (n := 2) (by norm_num)
  have hweight : 0 < law.weight ({i} : MutationMask 2) := by
    rw [law.singletonWeight_eq_oneBitMass_div (by norm_num) i, hmassOne]
    norm_num
  have hpositiveAccepted : 0 < law.maskEventMass
      (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1) :=
    lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1)
        i hacceptedHigh)
  have hslice : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.secondCoordinateSlice
        (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1) i := by
    change ({i} : MutationMask 2) ∈
      (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1).filter
        (fun mask => i ∈ mask)
    exact Finset.mem_filter.mpr ⟨hhigh, by simp⟩
  have hpositiveTailCoordinate : 0 <
      law.highRadiusCoordinateFlipMass 1 i := by
    rw [← law.maskEventMass_highRadius_coordinateSlice_eq 1 i]
    exact lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.secondCoordinateSlice
          (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1) i)
        i hslice)
  have haccSub :
      StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1 ⊆
      StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1 := by
    intro mask hm
    change mask ∈
      (StaticUnaryUnbiasedMutation.highRadiusMaskEvent (n := 2) 1).filter
        (fun m => Accepts (linearFitness w) x (mutateWithMask x m)) at hm
    exact (Finset.mem_filter.mp hm).1
  have _momentIdentity := law.tailMeanRadius_eq_radius_sum 1
  have _momentNonnegative := law.tailMeanRadius_nonneg 1
  have _momentBound := law.tailMeanRadius_le_meanRadius 1
  have _coordinateExchangeability :=
    law.highRadiusCoordinateFlipMass_eq 1 i (0 : Fin 2)
  have _coordinateDoubleCount :=
    law.sum_highRadiusCoordinateFlipMass_eq_tailMeanRadius 1
  have _coordinateMarginal :=
    law.highRadiusCoordinateFlipMass_eq_tailMeanRadius_div
      (by norm_num) 1 i
  have _sliceIdentity :=
    law.maskEventMass_highRadius_coordinateSlice_eq 1 i
  have _sliceBound :=
    law.maskEventMass_slice_le_highRadiusCoordinateFlipMass
      1 (StaticUnaryUnbiasedMutation.acceptedHighRadiusMaskEvent w x 1)
      haccSub i
  have _acceptedLoss :=
    law.acceptedHighRadiusFlippedOneLoss_le_tailMeanRadius
      (by norm_num) w g x 1 hg
  have _acceptedTailDrop :=
    law.acceptedHighRadiusPotentialDrop_ge_neg_tailMeanRadius
      (by norm_num) w g x 1 hg
  have _signedDrift :=
    law.linearErrorPotential_drift_ge_short_sub_tailMeanRadius
      (by norm_num) w g x 1 hg
  trivial

/-- The twelfth Stage 92 theorem has an explicit *short-radius gain premise*.
This example actually proves that premise, rather than leaving an unapplied
implication. For the all-one parent the singleton gain sum is zero; at cutoff
zero the short-radius event is empty, so the required inequality holds.
The independent preceding witness exercises nonzero accepted tail mass. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let g : Fin 2 → ℝ := fun _ => 1
  let y : BitString 2 := allOnes 2
  have hg : ∀ j : Fin 2, 0 ≤ g j := by
    intro j
    norm_num [g]
  have hzero : ECRuntime.zeroPositions y = ∅ := by
    ext j
    simp [ECRuntime.zeroPositions, y, allOnes]
  have hshortSet :
      StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) 0 = ∅ := by
    ext mask
    simp [StaticUnaryUnbiasedMutation.shortRadiusMaskEvent]
  have hshort :
      (law.oneBitMass / (2 : ℝ)) *
          (∑ j ∈ ECRuntime.zeroPositions y, g j) ≤
      law.acceptedEventWeightedPotentialDrop
        (StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) 0)
        w g y := by
    rw [hzero, hshortSet]
    simp [StaticUnaryUnbiasedMutation.acceptedEventWeightedPotentialDrop]
  have _conditionalDrift :=
    law.linearErrorPotential_drift_ge_singleton_sub_tailMeanRadius
      (by norm_num) w g y 0 hg hshort
  trivial



/-- Stage 93 non-vacuity. The normalized uniform one-bit law at `n = 2`
contains an accepted improving singleton in a genuine short-radius pivot event,
with strictly positive mutation mass. All eleven interfaces are instantiated
on the same positive objective/potential coefficients and non-optimal parent.
For the final budget theorem, we use the *actual* non-singleton remainder loss
as its budget: no unjustified positive-drift assertion is introduced. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let g : Fin 2 → ℝ := fun _ => 1
  let x : BitString 2 := allZeros 2
  let i : Fin 2 := 0
  let b : ℕ := 2
  let event : Finset (MutationMask 2) :=
    StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) b
  have hn : 0 < (2 : ℕ) := by norm_num
  have hb : 2 ≤ b := by norm_num [b]
  have hw : PositiveLinearWeights w := by
    intro j
    norm_num [w]
  have hg : ∀ j : Fin 2, 0 ≤ g j := by
    intro j
    norm_num [g]
  have hi : x i = false := by rfl
  have hzero : i ∈ ECRuntime.zeroPositions x :=
    (ECRuntime.mem_zeroPositions x i).2 hi
  have hsingle : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.shortAcceptedPivotEvent w x b i :=
    StaticUnaryUnbiasedMutation.singleton_mem_shortAcceptedPivotEvent
      w hw x b hb i hi
  have hrestricted : ({i} : MutationMask 2) ∈
      StaticUnaryUnbiasedMutation.restrictedAcceptedPivotEvent event w x i :=
    hsingle
  have haccept : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask 2)) :=
    StaticUnaryUnbiasedMutation.restrictedAcceptedPivotEvent_accepts
      event w x i ({i} : MutationMask 2) hrestricted
  have hp1 : law.oneBitMass = 1 :=
    StaticUnaryUnbiasedMutation.uniformOneBitLaw_oneBitMass
      (n := 2) (by norm_num)
  have hweight : 0 < law.weight ({i} : MutationMask 2) := by
    rw [law.singletonWeight_eq_oneBitMass_div hn i, hp1]
    norm_num
  have hpositiveEvent : 0 < law.maskEventMass
      (StaticUnaryUnbiasedMutation.shortAcceptedPivotEvent w x b i) :=
    lt_of_lt_of_le hweight
      (law.singletonWeight_le_maskEventMass
        (StaticUnaryUnbiasedMutation.shortAcceptedPivotEvent w x b i)
        i hsingle)
  have hacceptsAll : ∀ mask ∈
      StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b i,
      Accepts (linearFitness w) x (mutateWithMask x mask) := by
    intro mask hm
    exact StaticUnaryUnbiasedMutation.shortPivotRemainderEvent_accepts
      w x b i mask hm
  let budget : Fin 2 → ℝ := fun j =>
    law.acceptedEventFlippedOneLoss
      (StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b j) g x
  have hbudget : ∀ j ∈ ECRuntime.zeroPositions x,
      law.acceptedEventFlippedOneLoss
        (StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b j) g x ≤
        budget j := by
    intro j hj
    exact le_refl _
  have _arbitraryEventPivotPartition :=
    law.acceptedEventWeightedPotentialDrop_event_eq_sum_pivot_slices
      event w g hw x
  have _shortPivotPartition :=
    law.acceptedEventWeightedPotentialDrop_short_eq_sum_pivots
      w g hw x b
  have _singletonMembership := hsingle
  have _singletonRemainderIdentity :=
    law.shortAcceptedPivotEvent_drop_eq_singleton_add_remainder
      hn w g hw x b hb i hi
  have _shortSingletonSumIdentity :=
    law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_remainders
      hn w g hw x b hb
  have _acceptedLossBound :=
    law.acceptedEventWeightedPotentialDrop_ge_neg_flippedOneLoss_of_accepts
      (StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b i)
      w g x hg hacceptsAll
  have _remainderAccepted := hacceptsAll
  have _shortPivotLossBound :=
    law.acceptedEventWeightedPotentialDrop_short_ge_singleton_sub_pivotLoss
      hn w g hw x b hb hg
  have _globalSignedDriftBound :=
    law.linearErrorPotential_drift_ge_singleton_sub_pivotLoss_sub_tailMeanRadius
      hn w g hw x b hb hg
  have _pivotBudgetBound :=
    law.linearErrorPotential_drift_ge_singleton_sub_pivotBudgets_sub_tailMeanRadius
      hn w g hw x b hb hg budget hbudget
  trivial

end ECRuntimeTest
