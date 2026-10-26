import ECRuntime.AdaptiveLeadingOnesExactUniformRuntime
import ECRuntime.AdaptiveLeadingOnesScheduleExitComparison
import ECRuntime.AdaptiveLeadingOnesTrajectoryRuntimeAssembly
import ECRuntime.AdaptiveLeadingOnesUniquePositiveLevelOptimizer
import ECRuntime.AdditiveDrift
import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.CouplingDomination
import ECRuntime.DoerrDoerrMonotoneUniformMean
import ECRuntime.Drift
import ECRuntime.GenericFixedTargetAdditiveDriftLower
import ECRuntime.JumpEscapeOptimalRate
import ECRuntime.JumpPlateauEscape
import ECRuntime.LeadingOnesBoundaryRuntimeInfimum
import ECRuntime.LeadingOnesFixedTargetCandidate
import ECRuntime.LeadingOnesOptimalRate
import ECRuntime.LeadingOnesReferenceExitCostBoundaryTendsto
import ECRuntime.LeadingOnesStrictPositivePolicyOptimality
import ECRuntime.LevelExitDomination
import ECRuntime.MultiplicativeDrift
import ECRuntime.MultiplicativeDriftTail
import ECRuntime.OneMaxEAThresholdRuntimeLower
import ECRuntime.OneMaxUnaryStochasticDomination
import ECRuntime.RLSAllDimensionPaperCenteredExact
import ECRuntime.RLSAllDimensionPaperSharpCentered
import ECRuntime.RLSFixedBudget
import ECRuntime.RLSFixedTarget
import ECRuntime.RLSStrictMonotoneFixedTargetExact
import ECRuntime.RLSUniformInitialFixedBudgetMean
import ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
import ECRuntime.RandomStakeCouponArbitraryTargetRuntime
import ECRuntime.RandomStakeCouponFinitePaperCenteredExact
import ECRuntime.RandomStakeCouponSharpPaperCentered
import ECRuntime.RandomStakeCouponStatewiseSurvivalCorrespondence
import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import ECRuntime.StaticUnarySecondFactorialRadiusBound
import ECRuntime.StaticUnaryUnbiasedCorrectedRuntime
import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import ECRuntime.StaticUnaryUnbiasedSharpMomentUpper
import ECRuntime.StochasticDomination
import ECRuntime.UnaryOneMaxHarmonicLowerScaled
import ECRuntime.UnaryOneMaxThresholdRuntimeLower
import ECRuntime.WittStandardRuntimeAsymptotics

/-!
# Axiom audit for the theorems cited in `docs/current/papers/`

Every theorem that a paper file in `docs/current/papers/` cites as evidence for a paper-level
claim must depend on exactly `propext`, `Classical.choice` and `Quot.sound`.
This extends `AxiomAudit` beyond the six historical facades; theorems already
audited there are not repeated.

Generated from real compiler output, never written by hand.
-/

/-- info: 'ECRuntime.leadingOnes_scaled_fixedRate_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnes_scaled_fixedRate_limit

/-- info: 'ECRuntime.leadingOnes_fixedRate_unique_optimum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnes_fixedRate_unique_optimum

/-- info: 'ECRuntime.proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum

/-- info: 'ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum

/-- info: 'ECRuntime.proposed_leadingOnes_positiveLevelExit_uniqueMaximizer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnes_positiveLevelExit_uniqueMaximizer

/-- info: 'ECRuntime.proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff

/-- info: 'ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass

/-- info: 'ECRuntime.proposed_leadingOnes_referenceRuntime_boundaryInfimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnes_referenceRuntime_boundaryInfimum

/-- info: 'ECRuntime.proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto

/-- info: 'ECRuntime.proposed_randomStakeCoupon_allDimensionPaperSharpCentered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_randomStakeCoupon_allDimensionPaperSharpCentered

/-- info: 'ECRuntime.proposed_randomStakeCoupon_finitePaperCenteredExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_randomStakeCoupon_finitePaperCenteredExact

/-- info: 'ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperSharpCentered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperSharpCentered

/-- info: 'ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperCentered_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperCentered_exact

/-- info: 'ECRuntime.proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS

/-- info: 'ECRuntime.proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS

/-- info: 'ECRuntime.proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS

/-- info: 'ECRuntime.proposed_binomialHarmonicAverage_closedForm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_binomialHarmonicAverage_closedForm

/-- info: 'ECRuntime.proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS

/-- info: 'ECRuntime.proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection

/-- info: 'ECRuntime.proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS

/-- info: 'ECRuntime.additiveDrift_runtimeSup_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.additiveDrift_runtimeSup_le

/-- info: 'ECRuntime.additiveDrift_finiteHorizonBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.additiveDrift_finiteHorizonBound

/-- info: 'ECRuntime.expectedValueAfter_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.expectedValueAfter_mono

/-- info: 'ECRuntime.additiveDrift_superSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.additiveDrift_superSolution

/-- info: 'ECRuntime.multiplicativeDrift_runtimeSup_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.multiplicativeDrift_runtimeSup_le

/-- info: 'ECRuntime.multiplicativeDrift_finiteHorizonBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.multiplicativeDrift_finiteHorizonBound

/-- info: 'ECRuntime.multiplicativeDrift_firstHittingTime_tailMass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.multiplicativeDrift_firstHittingTime_tailMass_le

/-- info: 'ECRuntime.wittStandard_runtimeSup_le_asymptotic_upperBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittStandard_runtimeSup_le_asymptotic_upperBound

/-- info: 'ECRuntime.proposed_genericFixedTarget_additiveDrift_runtimeLower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_genericFixedTarget_additiveDrift_runtimeLower

/-- info: 'ECRuntime.stochasticallyDominated_by_geometricWaitingSum_of_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.stochasticallyDominated_by_geometricWaitingSum_of_coupling

/-- info: 'ECRuntime.natTailDominated_by_geometricWaitingSum_of_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.natTailDominated_by_geometricWaitingSum_of_coupling

/-- info: 'ECRuntime.natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime

/-- info: 'ECRuntime.stochasticallyDominated_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.stochasticallyDominated_refl

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.oneMaxUnary_hittingTime_stochasticDomination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.oneMaxUnary_hittingTime_stochasticDomination

/-- info: 'ECRuntime.rlsLinear_fixedTarget_runtimeSup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.rlsLinear_fixedTarget_runtimeSup_eq

/-- info: 'ECRuntime.proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates

/-- info: 'ECRuntime.proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum

/-- info: 'ECRuntime.proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np

/-- info: 'ECRuntime.proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius

/-- info: 'ECRuntime.rlsLinear_fixedBudget_expectedZeros_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.rlsLinear_fixedBudget_expectedZeros_eq

/-- info: 'ECRuntime.proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros

/-- info: 'ECRuntime.jump_plateau_oneStepSuccessMass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.jump_plateau_oneStepSuccessMass

/-- info: 'ECRuntime.jump_plateau_runtimeSup_eq_geometricMean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.jump_plateau_runtimeSup_eq_geometricMean

/-- info: 'ECRuntime.jump_plateau_runtimeTail_eq_geometric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.jump_plateau_runtimeTail_eq_geometric

/-- info: 'ECRuntime.candidateJumpEscape_fixedRate_optimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.candidateJumpEscape_fixedRate_optimal

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.coordinateFlipMass_eq_meanRadius_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.coordinateFlipMass_eq_meanRadius_div

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le

/-- info: 'ECRuntime.proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap
