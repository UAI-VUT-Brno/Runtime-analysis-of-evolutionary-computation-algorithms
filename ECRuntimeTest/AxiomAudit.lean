import ECRuntime.LeadingOnesMainResults
import ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain
import ECRuntime.WittMutationLogThreeRuntime
import ECRuntime.WittStandardRuntimeAsymptotics
import ECRuntime.WittStandardRuntimeTail

/-!
# Axiom audit

Every facade theorem must depend on exactly the three standard Lean axioms
`propext`, `Classical.choice` and `Quot.sound` -- nothing else.

`#guard_msgs` turns each expectation below into a build error when it stops
holding, so the introduction of `sorry` (which shows up as `sorryAx`), a new
`axiom`, or `native_decide` cannot pass the build even when laundered through
an intermediate lemma.

These pins are generated from real compiler output, never written by hand.
-/

/-- info: 'ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_formula

/-- info: 'ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum

/-- info: 'ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula

/-- info: 'ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_ne_top

/-- info: 'ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.singletonRate_mul_correctedWeight_le_acceptedLeftWeightedContribution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.singletonRate_mul_correctedWeight_le_acceptedLeftWeightedContribution

/-- info: 'ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_correctedLeftDelta_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_correctedLeftDelta_nonneg

/-- info: 'ECRuntime.wittMutationLinearPotential_scaled_le_three_mul_n_of_le_logThreeScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittMutationLinearPotential_scaled_le_three_mul_n_of_le_logThreeScale

/-- info: 'ECRuntime.wittMutation_runtimeSup_le_logThreeScale_log_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittMutation_runtimeSup_le_logThreeScale_log_bound

/-- info: 'ECRuntime.wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale

/-- info: 'ECRuntime.wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_logThreeScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_logThreeScale

/-- info: 'ECRuntime.wittMutationExactRateRuntimeLeadingFactor_one_le_logThreeScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittMutationExactRateRuntimeLeadingFactor_one_le_logThreeScale

/-- info: 'ECRuntime.wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale

/-- info: 'ECRuntime.wittStandard_runtimeSup_le_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittStandard_runtimeSup_le_log_bound

/-- info: 'ECRuntime.wittStandard_runtimeSup_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittStandard_runtimeSup_ne_top

/-- info: 'ECRuntime.wittStandard_runtimeSup_le_leading_add_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittStandard_runtimeSup_le_leading_add_linear

/-- info: 'ECRuntime.wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n

/-- info: 'ECRuntime.wittStandard_firstHittingTime_tailMass_le_geometric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ECRuntime.wittStandard_firstHittingTime_tailMass_le_geometric
