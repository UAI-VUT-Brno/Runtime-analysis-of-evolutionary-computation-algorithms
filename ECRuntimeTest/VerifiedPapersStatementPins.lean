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
# Statement pins for the theorems cited in `docs/current/papers/`

Freezes the elaborated type of every theorem that `docs/current/papers/` cites
as evidence for a paper-level claim, so the document cannot silently drift from
the statements it describes. Theorems already pinned in `StatementPins` are not
repeated. A deliberate statement change regenerates the pin in the same commit.

Generated from real compiler output, never written by hand.
-/

/-- info: ECRuntime.leadingOnes_scaled_fixedRate_limit : ∀ (c : ℝ),
  0 < c →
    Filter.Tendsto
      (fun n => ECRuntime.leadingOnesUniformExpectedRuntimeFormula n (ECRuntime.scaledMutationRate c n) / ↑n ^ 2)
      Filter.atTop (nhds (ECRuntime.leadingOnesFixedRateCoefficient c))
-/
#guard_msgs in
#check @ECRuntime.leadingOnes_scaled_fixedRate_limit

/-- info: ECRuntime.leadingOnes_fixedRate_unique_optimum : ∃ c,
  1 < c ∧
    c < 2 ∧
      (2 - c) * Real.exp c = 2 ∧
        (∀ (d : ℝ), 0 < d → ECRuntime.leadingOnesFixedRateCoefficient c ≤ ECRuntime.leadingOnesFixedRateCoefficient d) ∧
          ∀ (d : ℝ), 1 < d → d < 2 → (2 - d) * Real.exp d = 2 → d = c
-/
#guard_msgs in
#check @ECRuntime.leadingOnes_fixedRate_unique_optimum

/-- info: ECRuntime.proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum : ∀ (n : ℕ)
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
  (rate : ℕ → ℝ) (hrate : ∀ j ≤ n, 0 ≤ rate j ∧ rate j ≤ 1),
  (∀ j ≤ n, 0 < rate j ∧ rate j < 1) →
    (↑(Fintype.card (ECRuntime.BitString n)))⁻¹ *
        ∑ x,
          ∫⁻ (path : ℕ → ECRuntime.BitString n),
            ECRuntime.transitionTrajectoryFirstHittingTime (ECRuntime.leadingOnesTarget n) x
              path ∂ECRuntime.transitionTrajectoryMeasure (ECRuntime.leadingOnesAdaptiveTransition rate) ⋯ x =
      ENNReal.ofReal (1 / 2 * ∑ i, (rate ↑i * (1 - rate ↑i) ^ ↑i)⁻¹)
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum

/-- info: ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum : ∀ (n : ℕ)
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
  (rate : ℕ → ℝ) (hrate : ∀ j ≤ n, 0 ≤ rate j ∧ rate j ≤ 1),
  (∀ j ≤ n, 0 < rate j ∧ rate j < 1) →
    ECRuntime.leadingOnesAdaptiveUniformFirstHittingTimeExpectation n rate hrate =
      ENNReal.ofReal (1 / 2 * ∑ i, (rate ↑i * (1 - rate ↑i) ^ ↑i)⁻¹)
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum

/-- info: ECRuntime.proposed_leadingOnes_positiveLevelExit_uniqueMaximizer : ∀ (j : ℕ),
  0 < j → ∀ (p : ℝ), 0 ≤ p → p ≤ 1 → p * (1 - p) ^ j = 1 / ↑(j + 1) * (1 - 1 / ↑(j + 1)) ^ j → p = 1 / ↑(j + 1)
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnes_positiveLevelExit_uniqueMaximizer

/-- info: ECRuntime.proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff : ∀ (n : ℕ)
  [inst : MeasurableSpace (ECRuntime.BitString n)] [MeasurableSingletonClass (ECRuntime.BitString n)] (base : ℝ),
  0 < base →
    base < 1 →
      ∀ (rate : ℕ → ℝ),
        (∀ j ≤ n, 0 < rate j ∧ rate j < 1) →
          rate 0 = base →
            (↑(Fintype.card (ECRuntime.BitString n)))⁻¹ *
                  ∑ x,
                    ECRuntime.runtimeSup (ECRuntime.leadingOnesAdaptiveTransition rate) (ECRuntime.leadingOnesTarget n)
                      x =
                (↑(Fintype.card (ECRuntime.BitString n)))⁻¹ *
                  ∑ x,
                    ECRuntime.runtimeSup
                      (ECRuntime.leadingOnesAdaptiveTransition
                        (ECRuntime.proposed_leadingOnes_referenceOptimalRate base))
                      (ECRuntime.leadingOnesTarget n) x →
              ∀ (i : Fin n), 0 < ↑i → rate ↑i = ECRuntime.proposed_leadingOnes_referenceOptimalRate base ↑i
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff

/-- info: ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass : ∀ (n : ℕ)
  [inst : MeasurableSpace (ECRuntime.BitString n)] [MeasurableSingletonClass (ECRuntime.BitString n)]
  (rate₁ rate₂ : ℕ → ℝ),
  (∀ j ≤ n, 0 < rate₁ j ∧ rate₁ j < 1) →
    (∀ j ≤ n, 0 < rate₂ j ∧ rate₂ j < 1) →
      (∀ (i : Fin n), rate₁ ↑i * (1 - rate₁ ↑i) ^ ↑i ≤ rate₂ ↑i * (1 - rate₂ ↑i) ^ ↑i) →
        (↑(Fintype.card (ECRuntime.BitString n)))⁻¹ *
            ∑ x,
              ECRuntime.runtimeSup (ECRuntime.leadingOnesAdaptiveTransition rate₂) (ECRuntime.leadingOnesTarget n) x ≤
          (↑(Fintype.card (ECRuntime.BitString n)))⁻¹ *
            ∑ x, ECRuntime.runtimeSup (ECRuntime.leadingOnesAdaptiveTransition rate₁) (ECRuntime.leadingOnesTarget n) x
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass

/-- info: ECRuntime.proposed_leadingOnes_referenceRuntime_boundaryInfimum : ∀ (n : ℕ),
  0 < n →
    ∀ [inst : MeasurableSpace (ECRuntime.BitString n)] [MeasurableSingletonClass (ECRuntime.BitString n)],
      Filter.Tendsto
        (fun base =>
          (↑(Fintype.card (ECRuntime.BitString n)))⁻¹ *
            ∑ x,
              ECRuntime.runtimeSup
                (ECRuntime.leadingOnesAdaptiveTransition (ECRuntime.proposed_leadingOnes_referenceOptimalRate base))
                (ECRuntime.leadingOnesTarget n) x)
        (nhdsWithin 1 (Set.Iio 1))
        (nhds (1 / 2 + ∑ i with 0 < ↑i, 1 / 2 * ENNReal.ofReal (1 / ↑(↑i + 1) * (1 - 1 / ↑(↑i + 1)) ^ ↑i)⁻¹))
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnes_referenceRuntime_boundaryInfimum

/-- info: ECRuntime.proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto : ∀ (n : ℕ),
  Filter.Tendsto
    (fun base =>
      ∑ i,
        1 / 2 *
          ENNReal.ofReal
            (ECRuntime.proposed_leadingOnes_referenceOptimalRate base ↑i *
                (1 - ECRuntime.proposed_leadingOnes_referenceOptimalRate base ↑i) ^ ↑i)⁻¹)
    (nhdsWithin 1 (Set.Iio 1))
    (nhds (∑ i, if ↑i = 0 then 1 / 2 else 1 / 2 * ENNReal.ofReal (1 / ↑(↑i + 1) * (1 - 1 / ↑(↑i + 1)) ^ ↑i)⁻¹))
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto

/-- info: ECRuntime.proposed_randomStakeCoupon_allDimensionPaperSharpCentered : Filter.Tendsto
  (fun n =>
    if hn : 0 < n then
      (∑ x, (ECRuntime.runtimeSup (ECRuntime.randomStakeCouponTransition hn) {ECRuntime.allOnes n} x).toReal) / 2 ^ n -
        ↑n * ((ECRuntime.harmonicReal (n / 2) + ECRuntime.harmonicReal ((n + 1) / 2)) / 2)
    else 0)
  Filter.atTop (nhds (-(1 / 2)))
-/
#guard_msgs in
#check @ECRuntime.proposed_randomStakeCoupon_allDimensionPaperSharpCentered

/-- info: @ECRuntime.proposed_randomStakeCoupon_finitePaperCenteredExact : ∀ {n : ℕ} (hn : 0 < n),
  (∑ x, (ECRuntime.runtimeSup (ECRuntime.randomStakeCouponTransition hn) {ECRuntime.allOnes n} x).toReal) / 2 ^ n -
      ↑n * ((ECRuntime.harmonicReal (n / 2) + ECRuntime.harmonicReal ((n + 1) / 2)) / 2) =
    ↑n *
      (ECRuntime.harmonicReal n - ∑ j ∈ Finset.Icc 1 n, 1 / (↑j * 2 ^ j) -
        (ECRuntime.harmonicReal (n / 2) + ECRuntime.harmonicReal ((n + 1) / 2)) / 2)
-/
#guard_msgs in
#check @ECRuntime.proposed_randomStakeCoupon_finitePaperCenteredExact

/-- info: ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperSharpCentered : ∀ (fitness : (n : ℕ) → ECRuntime.BitString n → ℝ),
  (∀ (n : ℕ), ECRuntime.CandidateCoordinateStrictMonotonicity (fitness n)) →
    Filter.Tendsto
      (fun n =>
        if hn : 0 < n then
          ECRuntime.strictMonotoneRLSUniformInitialMean hn (fitness n) -
            ↑n * ((ECRuntime.harmonicReal (n / 2) + ECRuntime.harmonicReal ((n + 1) / 2)) / 2)
        else 0)
      Filter.atTop (nhds (-(1 / 2)))
-/
#guard_msgs in
#check @ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperSharpCentered

/-- info: @ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperCentered_exact : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ECRuntime.strictMonotoneRLSUniformInitialMean hn fitness -
        ↑n * ((ECRuntime.harmonicReal (n / 2) + ECRuntime.harmonicReal ((n + 1) / 2)) / 2) =
      ↑n *
        (ECRuntime.harmonicReal n - ∑ j ∈ Finset.Icc 1 n, 1 / (↑j * 2 ^ j) -
          (ECRuntime.harmonicReal (n / 2) + ECRuntime.harmonicReal ((n + 1) / 2)) / 2)
-/
#guard_msgs in
#check @ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperCentered_exact

/-- info: @ECRuntime.proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ∀ (t : ℕ) (x : ECRuntime.BitString n),
      ECRuntime.finiteLevelSurvival (ECRuntime.randomStakeCouponTransition hn) {ECRuntime.allOnes n}ᶜ t x =
        ECRuntime.finiteLevelSurvival ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          {ECRuntime.allOnes n}ᶜ t x
-/
#guard_msgs in
#check @ECRuntime.proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS

/-- info: @ECRuntime.proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ∀ (target : Set (ECRuntime.BitString n)) (x : ECRuntime.BitString n),
      ECRuntime.runtimeSup (ECRuntime.randomStakeCouponTransition hn) target x =
        ECRuntime.runtimeSup ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness) target x
-/
#guard_msgs in
#check @ECRuntime.proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS

/-- info: @ECRuntime.proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ∀ (target : Set (ECRuntime.BitString n)) [inst : DecidablePred fun x => x ∈ target] (t : ℕ)
      (x : ECRuntime.BitString n),
      ECRuntime.finiteLevelSurvival (ECRuntime.randomStakeCouponTransition hn) targetᶜ t x =
        ECRuntime.finiteLevelSurvival ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x
-/
#guard_msgs in
#check @ECRuntime.proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS

/-- info: ECRuntime.proposed_binomialHarmonicAverage_closedForm : ∀ (n : ℕ),
  (∑ k ∈ Finset.range (n + 1), ↑(n.choose k) * ECRuntime.harmonicReal k) / 2 ^ n =
    ECRuntime.harmonicReal n - ∑ j ∈ Finset.Icc 1 n, 1 / (↑j * 2 ^ j)
-/
#guard_msgs in
#check @ECRuntime.proposed_binomialHarmonicAverage_closedForm

/-- info: @ECRuntime.proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ∀ (target : Set (ECRuntime.BitString n)) (horizon : ℕ) (weight : ℕ → ℝ) (x : ECRuntime.BitString n),
      ∑ t ∈ Finset.range horizon,
          weight t * ECRuntime.finiteLevelSurvival (ECRuntime.randomStakeCouponTransition hn) targetᶜ t x =
        ∑ t ∈ Finset.range horizon,
          weight t *
            ECRuntime.finiteLevelSurvival
              ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness) targetᶜ t x
-/
#guard_msgs in
#check @ECRuntime.proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS

/-- info: @ECRuntime.proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ECRuntime.strictMonotoneRLSUniformInitialMean hn fitness =
      ↑n * (ECRuntime.harmonicReal n - ∑ j ∈ Finset.Icc 1 n, 1 / (↑j * 2 ^ j))
-/
#guard_msgs in
#check @ECRuntime.proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection

/-- info: @ECRuntime.proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ∀ (x : ECRuntime.BitString n),
      ECRuntime.runtimeSup (ECRuntime.randomStakeCouponTransition hn) {ECRuntime.allOnes n} x =
        ECRuntime.runtimeSup ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          {ECRuntime.allOnes n} x
-/
#guard_msgs in
#check @ECRuntime.proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS

/-- info: @ECRuntime.additiveDrift_runtimeSup_le : ∀ {α : Type u_1} [inst : Fintype α] (P : ECRuntime.TransitionMatrix α)
  (target : Set α) [inst_1 : DecidablePred fun x => x ∈ target] (V : α → ℝ) (δ : ℝ),
  ECRuntime.IsStochastic P →
    0 < δ →
      (∀ (x : α), 0 ≤ V x) →
        (∀ x ∈ target, V x = 0) →
          (∀ x ∉ target, δ ≤ ECRuntime.driftAt P V x) →
            ∀ (x : α), ECRuntime.runtimeSup P target x ≤ ENNReal.ofReal (ECRuntime.additiveDriftRuntime δ V x)
-/
#guard_msgs in
#check @ECRuntime.additiveDrift_runtimeSup_le

/-- info: @ECRuntime.additiveDrift_finiteHorizonBound : ∀ {α : Type u_1} [inst : Fintype α] (P : ECRuntime.TransitionMatrix α)
  (target : Set α) [inst_1 : DecidablePred fun x => x ∈ target] (V : α → ℝ) (δ : ℝ),
  ECRuntime.IsStochastic P →
    0 < δ →
      (∀ (x : α), 0 ≤ V x) →
        (∀ x ∈ target, V x = 0) →
          (∀ x ∉ target, δ ≤ ECRuntime.driftAt P V x) →
            ECRuntime.HasUniformFiniteHorizonRuntimeBound P target (ECRuntime.additiveDriftRuntime δ V)
-/
#guard_msgs in
#check @ECRuntime.additiveDrift_finiteHorizonBound

/-- info: @ECRuntime.expectedValueAfter_mono : ∀ {α : Type u_1} [inst : Fintype α] (P : ECRuntime.TransitionMatrix α),
  ECRuntime.IsStochastic P →
    ∀ (V W : α → ℝ),
      (∀ (y : α), V y ≤ W y) → ∀ (x : α), ECRuntime.expectedValueAfter P V x ≤ ECRuntime.expectedValueAfter P W x
-/
#guard_msgs in
#check @ECRuntime.expectedValueAfter_mono

/-- info: @ECRuntime.additiveDrift_superSolution : ∀ {α : Type u_1} [inst : Fintype α] (P : ECRuntime.TransitionMatrix α)
  (target : Set α) (V : α → ℝ) (δ : ℝ),
  0 < δ →
    (∀ x ∈ target, V x = 0) →
      (∀ x ∉ target, δ ≤ ECRuntime.driftAt P V x) →
        ECRuntime.IsRuntimeSuperSolution P target (ECRuntime.additiveDriftRuntime δ V)
-/
#guard_msgs in
#check @ECRuntime.additiveDrift_superSolution

/-- info: @ECRuntime.multiplicativeDrift_runtimeSup_le : ∀ {α : Type u_1} [inst : Fintype α] (P : ECRuntime.TransitionMatrix α)
  (V : α → ℝ) (δ vmin : ℝ),
  ECRuntime.IsStochastic P →
    0 < δ →
      0 < vmin →
        (∀ (z : α), 0 ≤ V z) →
          (∀ z ∉ ECRuntime.realPotentialTarget V, vmin ≤ V z) →
            ECRuntime.HasMultiplicativeDriftLowerBound P V δ →
              ∀ (x : α),
                ECRuntime.runtimeSup P (ECRuntime.realPotentialTarget V) x ≤
                  ENNReal.ofReal (ECRuntime.multiplicativeDriftRuntime δ vmin V x)
-/
#guard_msgs in
#check @ECRuntime.multiplicativeDrift_runtimeSup_le

/-- info: @ECRuntime.multiplicativeDrift_finiteHorizonBound : ∀ {α : Type u_1} [inst : Fintype α]
  (P : ECRuntime.TransitionMatrix α) (V : α → ℝ) (δ vmin : ℝ),
  ECRuntime.IsStochastic P →
    0 < δ →
      0 < vmin →
        (∀ (z : α), 0 ≤ V z) →
          (∀ z ∉ ECRuntime.realPotentialTarget V, vmin ≤ V z) →
            ECRuntime.HasMultiplicativeDriftLowerBound P V δ →
              ECRuntime.HasUniformFiniteHorizonRuntimeBound P (ECRuntime.realPotentialTarget V)
                (ECRuntime.multiplicativeDriftRuntime δ vmin V)
-/
#guard_msgs in
#check @ECRuntime.multiplicativeDrift_finiteHorizonBound

/-- info: @ECRuntime.multiplicativeDrift_firstHittingTime_tailMass_le : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : MeasurableSpace α] [inst_2 : MeasurableSingletonClass α] (P : ECRuntime.TransitionMatrix α)
  (hP : ECRuntime.IsStochastic P) (V : α → ℝ) (δ vmin : ℝ),
  0 ≤ δ →
    δ ≤ 1 →
      0 < vmin →
        (∀ z ∉ ECRuntime.realPotentialTarget V, vmin ≤ V z) →
          ECRuntime.HasMultiplicativeDriftLowerBound P V δ →
            ∀ x ∉ ECRuntime.realPotentialTarget V,
              ∀ (k : ℕ),
                ECRuntime.runtimeTailMass (ECRuntime.transitionTrajectoryMeasure P hP x)
                    (ECRuntime.transitionTrajectoryFirstHittingTime (ECRuntime.realPotentialTarget V) x) ↑k ≤
                  ENNReal.ofReal (vmin⁻¹ * V x * (1 - δ) ^ k)
-/
#guard_msgs in
#check @ECRuntime.multiplicativeDrift_firstHittingTime_tailMass_le

/-- info: @ECRuntime.wittStandard_runtimeSup_le_asymptotic_upperBound : ∀ {n : ℕ},
  4 ≤ n →
    ∀ (w : Fin n → ℝ),
      ECRuntime.PositiveLinearWeights w →
        ECRuntime.NonincreasingLinearWeights w →
          ∀ (x : ECRuntime.BitString n),
            ECRuntime.runtimeSup
                (ECRuntime.onePlusOneTransition (ECRuntime.standardMutationRate n) (ECRuntime.linearFitness w))
                (ECRuntime.oneMaxTarget n) x ≤
              ENNReal.ofReal (ECRuntime.wittStandardRuntimeUpperBound n)
-/
#guard_msgs in
#check @ECRuntime.wittStandard_runtimeSup_le_asymptotic_upperBound

/-- info: @ECRuntime.proposed_genericFixedTarget_additiveDrift_runtimeLower : ∀ {α : Type u_1} [inst : Fintype α]
  (P : ECRuntime.TransitionMatrix α),
  ECRuntime.IsStochastic P →
    ∀ (target : Set α) (potential : α → ℝ),
      (∀ (y : α), 0 ≤ potential y) →
        (∀ y ∈ target, potential y = 0) →
          ∀ (delta : ℝ),
            0 < delta →
              (∀ y ∉ target, ∑ z, P y z * (potential y - potential z) ≤ delta) →
                ∀ x ∉ target, ENNReal.ofReal (potential x / delta) ≤ ECRuntime.runtimeSup P target x
-/
#guard_msgs in
#check @ECRuntime.proposed_genericFixedTarget_additiveDrift_runtimeLower

/-- info: @ECRuntime.stochasticallyDominated_by_geometricWaitingSum_of_coupling : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω]
  {m : ℕ} (μ : MeasureTheory.Measure Ω) (X : Ω → ENNReal),
  Measurable X →
    ∀ (p : Fin m → ↑unitInterval) (κ : MeasureTheory.Measure (Ω × (Fin m → ENNReal))),
      MeasureTheory.Measure.map Prod.fst κ = μ →
        MeasureTheory.Measure.map Prod.snd κ = ECRuntime.geometricWaitingProductMeasure p →
          (∀ (z : Ω × (Fin m → ENNReal)), X z.1 ≤ ECRuntime.geometricWaitingSum z.2) →
            ECRuntime.StochasticallyDominated μ X (ECRuntime.geometricWaitingProductMeasure p)
              ECRuntime.geometricWaitingSum
-/
#guard_msgs in
#check @ECRuntime.stochasticallyDominated_by_geometricWaitingSum_of_coupling

/-- info: @ECRuntime.natTailDominated_by_geometricWaitingSum_of_coupling : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {m : ℕ}
  (μ : MeasureTheory.Measure Ω) (X : Ω → ENNReal),
  Measurable X →
    ∀ (p : Fin m → ↑unitInterval) (κ : MeasureTheory.Measure (Ω × (Fin m → ENNReal))),
      MeasureTheory.Measure.map Prod.fst κ = μ →
        MeasureTheory.Measure.map Prod.snd κ = ECRuntime.geometricWaitingProductMeasure p →
          (∀ (z : Ω × (Fin m → ENNReal)), X z.1 ≤ ECRuntime.geometricWaitingSum z.2) →
            ECRuntime.NatTailDominated μ X (ECRuntime.geometricWaitingProductMeasure p) ECRuntime.geometricWaitingSum
-/
#guard_msgs in
#check @ECRuntime.natTailDominated_by_geometricWaitingSum_of_coupling

/-- info: @ECRuntime.natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : MeasurableSpace α] [inst_2 : MeasurableSingletonClass α] (P : ECRuntime.TransitionMatrix α) (level : Set α)
  [inst_3 : DecidablePred fun z => z ∈ level] (hP : ECRuntime.IsStochastic P) (p : ↑unitInterval),
  p ≠ 0 →
    (∀ z ∈ level, ↑p ≤ ECRuntime.finiteEventMass (P z) fun y => y ∉ level) →
      ∀ x ∈ level,
        ECRuntime.NatTailDominated (ECRuntime.transitionTrajectoryMeasure P hP x)
          (ECRuntime.transitionTrajectoryFirstHittingTime levelᶜ x) (ECRuntime.geometricFailureMeasure p)
          ECRuntime.geometricWaitingTime
-/
#guard_msgs in
#check @ECRuntime.natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime

/-- info: @ECRuntime.stochasticallyDominated_refl : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
  (X : Ω → ENNReal), ECRuntime.StochasticallyDominated μ X μ X
-/
#guard_msgs in
#check @ECRuntime.stochasticallyDominated_refl

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.oneMaxUnary_hittingTime_stochasticDomination : ∀ {n : ℕ}
  (law : ECRuntime.StaticUnaryUnbiasedMutation n) (hn : 0 < n) (hp : 0 < law.oneBitMass)
  [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
  (x : ECRuntime.BitString n),
  ECRuntime.StochasticallyDominated (ECRuntime.transitionTrajectoryMeasure (law.transition ECRuntime.oneMaxReal) ⋯ x)
    (ECRuntime.transitionTrajectoryFirstHittingTime (ECRuntime.oneMaxTarget n) x)
    (ECRuntime.geometricWaitingSumMeasure (ECRuntime.geometricLevelProbabilityVector law.oneMaxGeometricRates ⋯ ⋯)) id
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.oneMaxUnary_hittingTime_stochasticDomination

/-- info: @ECRuntime.rlsLinear_fixedTarget_runtimeSup_eq : ∀ {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ),
  ECRuntime.PositiveLinearWeights w →
    ∀ (r : ℕ) (x : ECRuntime.BitString n),
      r ≤ ECRuntime.zeroCount x →
        ECRuntime.runtimeSup
            ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition (ECRuntime.linearFitness w))
            (ECRuntime.rlsZeroAtMost r) x =
          ENNReal.ofReal (↑n * (ECRuntime.harmonicReal (ECRuntime.zeroCount x) - ECRuntime.harmonicReal r))
-/
#guard_msgs in
#check @ECRuntime.rlsLinear_fixedTarget_runtimeSup_eq

/-- info: @ECRuntime.proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates : ∀ {n : ℕ} (hn : 0 < n)
  (fitness : ECRuntime.BitString n → ℝ),
  ECRuntime.CandidateCoordinateStrictMonotonicity fitness →
    ∀ (r : ℕ) (x : ECRuntime.BitString n),
      (ECRuntime.runtimeSup ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
            (ECRuntime.rlsZeroAtMost r) x).toReal =
        if ECRuntime.zeroCount x ≤ r then 0
        else ↑n * (ECRuntime.harmonicReal (ECRuntime.zeroCount x) - ECRuntime.harmonicReal r)
-/
#guard_msgs in
#check @ECRuntime.proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates

/-- info: @ECRuntime.proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum : ∀ {n : ℕ} {p : ℝ},
  0 < p →
    p < 1 →
      ∀ k ≤ n, ECRuntime.leadingOnesUniformFixedTargetMean n p k = 1 / 2 * ∑ i ∈ Finset.range k, (p * (1 - p) ^ i)⁻¹
-/
#guard_msgs in
#check @ECRuntime.proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum

/-- info: @ECRuntime.proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np : ∀ {n : ℕ},
  0 < n →
    ∀ (k : ℕ) (p : ℝ),
      0 < p →
        p ≤ 1 →
          ∀ (x : ECRuntime.BitString n),
            k < ECRuntime.zeroCount x →
              ENNReal.ofReal (↑(ECRuntime.zeroCount x - k) / (↑n * p)) ≤
                ECRuntime.runtimeSup (ECRuntime.onePlusOneTransition p ECRuntime.oneMaxReal)
                  {y | ECRuntime.zeroCount y ≤ k} x
-/
#guard_msgs in
#check @ECRuntime.proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np

/-- info: @ECRuntime.proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius : ∀ {n : ℕ},
  0 < n →
    ∀ (k : ℕ) (law : ECRuntime.StaticUnaryUnbiasedMutation n),
      0 < law.meanRadius →
        ∀ (x : ECRuntime.BitString n),
          k < ECRuntime.zeroCount x →
            ENNReal.ofReal (↑(ECRuntime.zeroCount x - k) / law.meanRadius) ≤
              ECRuntime.runtimeSup (law.transition ECRuntime.oneMaxReal) {y | ECRuntime.zeroCount y ≤ k} x
-/
#guard_msgs in
#check @ECRuntime.proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius

/-- info: @ECRuntime.rlsLinear_fixedBudget_expectedZeros_eq : ∀ {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ),
  ECRuntime.PositiveLinearWeights w →
    ∀ (x : ECRuntime.BitString n) (t : ℕ),
      ∑ path,
          ECRuntime.finiteTrajectoryWeight
              ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition (ECRuntime.linearFitness w)) t x
              path *
            ↑(ECRuntime.zeroCount (ECRuntime.finiteBudgetTerminal t x path)) =
        ↑(ECRuntime.zeroCount x) * (1 - 1 / ↑n) ^ t
-/
#guard_msgs in
#check @ECRuntime.rlsLinear_fixedBudget_expectedZeros_eq

/-- info: @ECRuntime.proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros : ∀ {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ),
  ECRuntime.PositiveLinearWeights w →
    ∀ (t : ℕ),
      (∑ x,
            ∑ path,
              ECRuntime.finiteTrajectoryWeight
                  ((ECRuntime.StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition (ECRuntime.linearFitness w)) t
                  x path *
                ↑(ECRuntime.zeroCount (ECRuntime.finiteBudgetTerminal t x path))) /
          2 ^ n =
        ↑n / 2 * (1 - 1 / ↑n) ^ t
-/
#guard_msgs in
#check @ECRuntime.proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros

/-- info: @ECRuntime.jump_plateau_oneStepSuccessMass : ∀ {n : ℕ} (law : ECRuntime.StaticUnaryUnbiasedMutation n) (k : ℕ),
  2 ≤ k →
    k < n →
      ∀ (x : ECRuntime.BitString n),
        ECRuntime.zeroCount x = k →
          (ECRuntime.finiteEventMass law.weight fun mask =>
              ECRuntime.selectedAfterMask (ECRuntime.jumpFitness k) x mask = ECRuntime.allOnes n) =
            law.radiusMass k / ↑(n.choose k)
-/
#guard_msgs in
#check @ECRuntime.jump_plateau_oneStepSuccessMass

/-- info: @ECRuntime.jump_plateau_runtimeSup_eq_geometricMean : ∀ {n : ℕ} (law : ECRuntime.StaticUnaryUnbiasedMutation n) (k : ℕ),
  2 ≤ k →
    k < n →
      0 < law.radiusMass k →
        ∀ (x : ECRuntime.BitString n),
          ECRuntime.zeroCount x = k →
            ECRuntime.runtimeSup (law.transition (ECRuntime.jumpFitness k)) {ECRuntime.allOnes n} x =
              ENNReal.ofReal (↑(n.choose k) / law.radiusMass k)
-/
#guard_msgs in
#check @ECRuntime.jump_plateau_runtimeSup_eq_geometricMean

/-- info: @ECRuntime.jump_plateau_runtimeTail_eq_geometric : ∀ {n : ℕ} (law : ECRuntime.StaticUnaryUnbiasedMutation n) (k : ℕ),
  2 ≤ k →
    k < n →
      0 < law.radiusMass k →
        ∀ [inst : MeasurableSpace (ECRuntime.BitString n)] [inst_1 : MeasurableSingletonClass (ECRuntime.BitString n)]
          (x : ECRuntime.BitString n),
          ECRuntime.zeroCount x = k →
            ∀ (t : ℕ),
              ECRuntime.runtimeTailMass
                  (ECRuntime.transitionTrajectoryMeasure (law.transition (ECRuntime.jumpFitness k)) ⋯ x)
                  (ECRuntime.transitionTrajectoryFirstHittingTime {ECRuntime.allOnes n} x) ↑t =
                ENNReal.ofReal ((1 - law.radiusMass k / ↑(n.choose k)) ^ t)
-/
#guard_msgs in
#check @ECRuntime.jump_plateau_runtimeTail_eq_geometric

/-- info: ECRuntime.candidateJumpEscape_fixedRate_optimal : ∀ (n k : ℕ),
  0 < k → k < n → ∀ (p : ℝ), 0 ≤ p → p ≤ 1 → p ^ k * (1 - p) ^ (n - k) ≤ (↑k / ↑n) ^ k * (1 - ↑k / ↑n) ^ (n - k)
-/
#guard_msgs in
#check @ECRuntime.candidateJumpEscape_fixedRate_optimal

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.coordinateFlipMass_eq_meanRadius_div : ∀ {n : ℕ}
  (law : ECRuntime.StaticUnaryUnbiasedMutation n), 0 < n → ∀ (i : Fin n), law.coordinateFlipMass i = law.meanRadius / ↑n
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.coordinateFlipMass_eq_meanRadius_div

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius : ∀ {n : ℕ}
  (law : ECRuntime.StaticUnaryUnbiasedMutation n), law.secondFactorialRadiusMoment ≤ ↑(n - 1) * law.meanRadius
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments : ∀
  {p₀ C₁ C₂ epsilon : ℝ},
  0 < p₀ →
    0 ≤ C₁ →
      0 ≤ C₂ →
        0 < epsilon →
          ∃ N,
            ∀ (n : ℕ),
              N ≤ n →
                ∀ (law : ECRuntime.StaticUnaryUnbiasedMutation n),
                  p₀ ≤ law.oneBitMass →
                    law.meanRadius ≤ C₁ →
                      law.secondFactorialRadiusMoment ≤ C₂ →
                        ∀ (w : Fin n → ℝ),
                          ECRuntime.PositiveLinearWeights w →
                            ECRuntime.NonincreasingLinearWeights w →
                              ∀ (x : ECRuntime.BitString n),
                                ECRuntime.runtimeSup (law.transition (ECRuntime.linearFitness w)) {ECRuntime.allOnes n}
                                    x ≤
                                  ENNReal.ofReal ((1 + epsilon) * (↑n * Real.log ↑n / law.oneBitMass))
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments

/-- info: @ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le : ∀ {n : ℕ}
  (law : ECRuntime.StaticUnaryUnbiasedMutation n),
  2 ≤ n →
    0 < law.oneBitMass →
      ∀ {alpha : ℝ},
        1 < alpha →
          ∀ (w : Fin n → ℝ),
            ECRuntime.PositiveLinearWeights w →
              ECRuntime.NonincreasingLinearWeights w →
                ∀ (x : ECRuntime.BitString n),
                  ECRuntime.runtimeSup (law.transition (ECRuntime.linearFitness w)) {ECRuntime.allOnes n} x ≤
                    ENNReal.ofReal
                      (ECRuntime.multiplicativeDriftRuntime (law.oneBitMass / ↑n * (1 - 1 / alpha)) 1
                        (law.correctedLinearPotential alpha w) x)
-/
#guard_msgs in
#check @ECRuntime.StaticUnaryUnbiasedMutation.correctedLinearPotential_runtimeSup_le

/-- info: @ECRuntime.proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap : ∀ {n : ℕ},
  0 < n →
    ∀ (law : ECRuntime.StaticUnaryUnbiasedMutation n) (chi : ℝ),
      0 < chi →
        ∀ (x : ECRuntime.BitString n),
          (∀ (y : ECRuntime.BitString n),
              (y != ECRuntime.allOnes n) = true →
                ∑ z,
                    law.transition ECRuntime.oneMaxReal y z *
                      (ECRuntime.harmonicReal (ECRuntime.zeroCount y) -
                        ECRuntime.harmonicReal (ECRuntime.zeroCount z)) ≤
                  chi / ↑n) →
            ENNReal.ofReal (↑n / chi * ECRuntime.harmonicReal (ECRuntime.zeroCount x)) ≤
              ECRuntime.runtimeSup (law.transition ECRuntime.oneMaxReal) {ECRuntime.allOnes n} x
-/
#guard_msgs in
#check @ECRuntime.proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap
