import ECRuntime.LeadingOnesMainResults
import ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain
import ECRuntime.WittMutationLogThreeRuntime
import ECRuntime.WittStandardRuntimeAsymptotics
import ECRuntime.WittStandardRuntimeTail

/-!
# Statement pins

`HISTORY.md` records, for twelve consecutive stages, that a *fix* round changes
no public theorem statement. Until now that was a prose promise. Each pin below
freezes the elaborated type of one facade theorem, so silently weakening a
hypothesis, adding one, or restating a conclusion becomes a build error.

A deliberate change to a promoted statement is a *stage*, not a fix: regenerate
the pin in the same commit and say so in `HISTORY.md`.

These pins are generated from real compiler output, never written by hand.
-/

/-- info: @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_formula : ∀ {n : ℕ}
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)] {p : ℝ}
  (hp0 : 0 < p) (hp1 : p < 1),
  ECRuntime.leadingOnesUniformFirstHittingTimeExpectation n p ⋯ ⋯ =
    ENNReal.ofReal (ECRuntime.leadingOnesUniformExpectedRuntimeFormula n p)
-/
#guard_msgs in
#check @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_formula

/-- info: @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum : ∀ {n : ℕ}
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)] {p : ℝ}
  (hp0 : 0 < p) (hp1 : p < 1),
  ECRuntime.leadingOnesUniformFirstHittingTimeExpectation n p ⋯ ⋯ = ENNReal.ofReal (1 / 2 * ∑ i, (p * (1 - p) ^ ↑i)⁻¹)
-/
#guard_msgs in
#check @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum

/-- info: @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula : ∀ {n : ℕ}
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)] {c : ℝ}
  (hc : 0 < c) (hn : 0 < n) (hcn : c < ↑n),
  ECRuntime.leadingOnesUniformFirstHittingTimeExpectation n (ECRuntime.scaledMutationRate c n) ⋯ ⋯ =
    ENNReal.ofReal (ECRuntime.leadingOnesUniformExpectedRuntimeFormula n (ECRuntime.scaledMutationRate c n))
-/
#guard_msgs in
#check @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula

/-- info: @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_ne_top : ∀ {n : ℕ}
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)] {c : ℝ}
  (hc : 0 < c) (hn : 0 < n) (hcn : c < ↑n),
  ECRuntime.leadingOnesUniformFirstHittingTimeExpectation n (ECRuntime.scaledMutationRate c n) ⋯ ⋯ ≠ ⊤
-/
#guard_msgs in
#check @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_ne_top

/-- info: @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm : ∀ {n : ℕ}
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
  (hn : 2 ≤ n),
  ECRuntime.leadingOnesUniformFirstHittingTimeExpectation n (ECRuntime.standardMutationRate n) ⋯ ⋯ =
    ENNReal.ofReal (ECRuntime.leadingOnesStandardRateClosedForm n)
-/
#guard_msgs in
#check @ECRuntime.leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.singletonRate_mul_correctedWeight_le_acceptedLeftWeightedContribution : ∀ {n : ℕ}
  (law : ECRuntime.StaticUnaryUnbiasedMutation n) {alpha : ℝ},
  0 ≤ alpha →
    ∀ (w : Fin n → ℝ),
      ECRuntime.PositiveLinearWeights w →
        ECRuntime.NonincreasingLinearWeights w →
          ∀ (x : ECRuntime.BitString n) (i : Fin n),
            x i = false →
              law.oneBitMass / ↑n * law.correctedPotentialWeight alpha w i ≤
                law.acceptedLeftWeightedContribution
                  (ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i)
                  (law.correctedPotentialWeight alpha w) x (law.correctedAnchor alpha w i)
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.singletonRate_mul_correctedWeight_le_acceptedLeftWeightedContribution

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_correctedLeftDelta_nonneg : ∀ {n : ℕ}
  (law : ECRuntime.StaticUnaryUnbiasedMutation n) {alpha : ℝ},
  0 ≤ alpha →
    ∀ (w : Fin n → ℝ),
      ECRuntime.PositiveLinearWeights w →
        ECRuntime.NonincreasingLinearWeights w →
          ∀ (x : ECRuntime.BitString n) (i : Fin n),
            ∀ mask ∈ ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i,
              0 ≤
                ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftDelta (law.correctedPotentialWeight alpha w) x mask
                  (law.correctedAnchor alpha w i)
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent_correctedLeftDelta_nonneg

/-- info: @ECRuntime.wittMutationLinearPotential_scaled_le_three_mul_n_of_le_logThreeScale : ∀ {n : ℕ},
  4 ≤ n →
    ∀ {c : ℝ},
      0 ≤ c →
        c ≤ ECRuntime.wittMutationC3LogThreeScale →
          ∀ (w : Fin n → ℝ) (x : ECRuntime.BitString n),
            ECRuntime.wittMutationLinearPotential (ECRuntime.scaledMutationRate c n) w x ≤ 3 * ↑n
-/
#guard_msgs in
#check @ECRuntime.wittMutationLinearPotential_scaled_le_three_mul_n_of_le_logThreeScale

/-- info: @ECRuntime.wittMutation_runtimeSup_le_logThreeScale_log_bound : ∀ {n : ℕ},
  4 ≤ n →
    ∀ {c : ℝ},
      0 < c →
        c ≤ ECRuntime.wittMutationC3LogThreeScale →
          ∀ (w : Fin n → ℝ),
            ECRuntime.PositiveLinearWeights w →
              ECRuntime.NonincreasingLinearWeights w →
                ∀ (x : ECRuntime.BitString n),
                  ECRuntime.runtimeSup
                      (ECRuntime.onePlusOneTransition (ECRuntime.scaledMutationRate c n) (ECRuntime.linearFitness w))
                      (ECRuntime.oneMaxTarget n) x ≤
                    ENNReal.ofReal (3 / c * ↑n * (1 + Real.log 3 + Real.log ↑n))
-/
#guard_msgs in
#check @ECRuntime.wittMutation_runtimeSup_le_logThreeScale_log_bound

/-- info: @ECRuntime.wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale : ∀ {n : ℕ},
  4 ≤ n →
    ∀ {c : ℝ},
      0 < c →
        c ≤ ECRuntime.wittMutationC3LogThreeScale →
          ∀ (w : Fin n → ℝ),
            ECRuntime.PositiveLinearWeights w →
              ECRuntime.NonincreasingLinearWeights w →
                ∀ (x : ECRuntime.BitString n),
                  ECRuntime.runtimeSup
                      (ECRuntime.onePlusOneTransition (ECRuntime.scaledMutationRate c n) (ECRuntime.linearFitness w))
                      (ECRuntime.oneMaxTarget n) x ≤
                    ENNReal.ofReal (ECRuntime.wittMutationExactRateRuntimeUpperBound c n)
-/
#guard_msgs in
#check @ECRuntime.wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale

/-- info: @ECRuntime.wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_logThreeScale : ∀ {c : ℝ},
  0 < c →
    c ≤ ECRuntime.wittMutationC3LogThreeScale →
      Filter.Tendsto (fun n => ECRuntime.wittMutationExactRateNormalizedRuntimeUpperBound c n) Filter.atTop
        (nhds (ECRuntime.wittMutationLeadingRuntimeFactor c))
-/
#guard_msgs in
#check @ECRuntime.wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_logThreeScale

/-- info: @ECRuntime.wittMutationExactRateRuntimeLeadingFactor_one_le_logThreeScale : ∀ {c : ℝ},
  0 < c →
    c ≤ ECRuntime.wittMutationC3LogThreeScale →
      ECRuntime.wittMutationLeadingRuntimeFactor 1 ≤ ECRuntime.wittMutationLeadingRuntimeFactor c
-/
#guard_msgs in
#check @ECRuntime.wittMutationExactRateRuntimeLeadingFactor_one_le_logThreeScale

/-- info: @ECRuntime.wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale : ∀ {n : ℕ} (hn : 4 ≤ n) {c : ℝ}
  (hc0 : 0 < c) (hc : c ≤ ECRuntime.wittMutationC3LogThreeScale) (w : Fin n → ℝ),
  ECRuntime.PositiveLinearWeights w →
    ECRuntime.NonincreasingLinearWeights w →
      ∀ [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
        (x : ECRuntime.BitString n),
        x ≠ ECRuntime.allOnes n →
          ∀ (r : ℝ),
            0 ≤ r →
              ∀ (k : ℕ),
                3 / c * ↑n * (Real.log 3 + Real.log ↑n + r) ≤ ↑k →
                  ECRuntime.runtimeTailMass (ECRuntime.linearScaledTrajectoryMeasureLogThree hn ⋯ hc w x)
                      (ECRuntime.transitionTrajectoryFirstHittingTime (ECRuntime.oneMaxTarget n) x) ↑k ≤
                    ENNReal.ofReal (Real.exp (-r))
-/
#guard_msgs in
#check @ECRuntime.wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale

/-- info: @ECRuntime.wittStandard_runtimeSup_le_log_bound : ∀ {n : ℕ},
  4 ≤ n →
    ∀ (w : Fin n → ℝ),
      ECRuntime.PositiveLinearWeights w →
        ECRuntime.NonincreasingLinearWeights w →
          ∀ (x : ECRuntime.BitString n),
            ECRuntime.runtimeSup
                (ECRuntime.onePlusOneTransition (ECRuntime.standardMutationRate n) (ECRuntime.linearFitness w))
                (ECRuntime.oneMaxTarget n) x ≤
              ENNReal.ofReal (Real.exp 1 * ↑n * (2 + Real.log ↑n))
-/
#guard_msgs in
#check @ECRuntime.wittStandard_runtimeSup_le_log_bound

/-- info: @ECRuntime.wittStandard_runtimeSup_ne_top : ∀ {n : ℕ},
  4 ≤ n →
    ∀ (w : Fin n → ℝ),
      ECRuntime.PositiveLinearWeights w →
        ECRuntime.NonincreasingLinearWeights w →
          ∀ (x : ECRuntime.BitString n),
            ECRuntime.runtimeSup
                (ECRuntime.onePlusOneTransition (ECRuntime.standardMutationRate n) (ECRuntime.linearFitness w))
                (ECRuntime.oneMaxTarget n) x ≠
              ⊤
-/
#guard_msgs in
#check @ECRuntime.wittStandard_runtimeSup_ne_top

/-- info: @ECRuntime.wittStandard_runtimeSup_le_leading_add_linear : ∀ {n : ℕ},
  4 ≤ n →
    ∀ (w : Fin n → ℝ),
      ECRuntime.PositiveLinearWeights w →
        ECRuntime.NonincreasingLinearWeights w →
          ∀ (x : ECRuntime.BitString n),
            ECRuntime.runtimeSup
                (ECRuntime.onePlusOneTransition (ECRuntime.standardMutationRate n) (ECRuntime.linearFitness w))
                (ECRuntime.oneMaxTarget n) x ≤
              ENNReal.ofReal
                (ECRuntime.wittStandardRuntimeLeadingTerm n + ECRuntime.wittStandardRuntimeLinearCorrection n)
-/
#guard_msgs in
#check @ECRuntime.wittStandard_runtimeSup_le_leading_add_linear

/-- info: ECRuntime.wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n : ∃ r,
  ECRuntime.NatIsBigO r ECRuntime.natLinearGrowth ∧
    ∀ (n : ℕ), ECRuntime.wittStandardRuntimeUpperBound n = ECRuntime.wittStandardRuntimeLeadingTerm n + r n
-/
#guard_msgs in
#check @ECRuntime.wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n

/-- info: @ECRuntime.wittStandard_firstHittingTime_tailMass_le_geometric : ∀ {n : ℕ} (hn : 4 ≤ n) (w : Fin n → ℝ),
  ECRuntime.PositiveLinearWeights w →
    ECRuntime.NonincreasingLinearWeights w →
      ∀ [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
        (x : ECRuntime.BitString n),
        x ≠ ECRuntime.allOnes n →
          ∀ (k : ℕ),
            ECRuntime.runtimeTailMass (ECRuntime.linearStandardTrajectoryMeasure ⋯ w x)
                (ECRuntime.transitionTrajectoryFirstHittingTime (ECRuntime.oneMaxTarget n) x) ↑k ≤
              ENNReal.ofReal (Real.exp 1 * ↑n * (1 - ECRuntime.wittStandardLinearDriftRate n) ^ k)
-/
#guard_msgs in
#check @ECRuntime.wittStandard_firstHittingTime_tailMass_le_geometric
