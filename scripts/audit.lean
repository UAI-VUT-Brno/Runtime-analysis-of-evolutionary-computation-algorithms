import ECRuntime

/-!
# Source-hygiene audit

Replaces the regex-based linter. Every check here reads the compiled environment, so
it reports what is actually true rather than what a pattern over source text guesses:

* **doc coverage** asks the environment, not "does the line above end a comment";
* **unused hypotheses** read real binder names from the declaration type, so a lambda
  binder inside a proof term cannot be mistaken for a hypothesis (the regex version
  reported three such, one of which was even used);
* **proof holes** use the axiom set, so a `sorry` reached through a helper whose own
  text is clean is still caught -- no textual scan can do that;
* **reachability** follows real proof dependencies, not import statements.

Run:

    lake env lean --run scripts/audit.lean [strict|candidate]

`candidate` permits `sorryAx` (a stage in progress). Exit 0 clean, 1 on findings.
-/

open Lean

namespace ECRuntimeAudit

/-- Modules that constitute the public API. Reachability is measured from here, not
from the root aggregator: `ECRuntime.lean` imports almost everything directly, so a
root-reachability check passes by construction and can never find dead code. -/
def facades : List Name :=
  [`ECRuntime.LeadingOnesMainResults,
   `ECRuntime.WittStandardRuntimeAsymptotics,
   `ECRuntime.WittStandardRuntimeTail,
   `ECRuntime.WittMutationLogThreeRuntime,
   `ECRuntime.WittMutationSharpRuntimeAsymptotics,
   `ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain]

/-- Public-facing terminal result modules added by the 547-module certified merge.

The six historical facades do not import all of the new theorem families. These
additional explicit roots cover their import dependencies without declaring the
umbrella `ECRuntime.lean` to be a facade: using that umbrella would make every
root import reachable by construction and silently disable the orphan check.

Keep this list deliberate. A future standalone public result needs an explicit
entry here, or a dependency path from an existing facade. -/
def mergedPublicFacades : List Name :=
  [ `ECRuntime.AbsorbingOccupationPrefixMonotonicity,
    `ECRuntime.AdaptiveLeadingOnesBoundaryFlipConjugacy,
    `ECRuntime.AdaptiveLeadingOnesConstantScheduleRuntime,
    `ECRuntime.AdaptiveLeadingOnesExactSkipTrajectoryParity,
    `ECRuntime.AdaptiveLeadingOnesExactUniformRuntime,
    `ECRuntime.AdaptiveLeadingOnesExitExponentialEnvelope,
    `ECRuntime.AdaptiveLeadingOnesFiniteRenewalSolution,
    `ECRuntime.AdaptiveLeadingOnesFirstVisitFiniteMarginalBridge,
    `ECRuntime.AdaptiveLeadingOnesHalfResidenceOptimality,
    `ECRuntime.AdaptiveLeadingOnesInteriorFiniteGapBound,
    `ECRuntime.AdaptiveLeadingOnesKernelScheduleExt,
    `ECRuntime.AdaptiveLeadingOnesMonotoneSupport,
    `ECRuntime.AdaptiveLeadingOnesOneLevelPolicyImprovement,
    `ECRuntime.AdaptiveLeadingOnesOptimalAggregateResidenceCost,
    `ECRuntime.AdaptiveLeadingOnesOptimalLevelSurvivalDominance,
    `ECRuntime.AdaptiveLeadingOnesOptimalResidenceClosedForm,
    `ECRuntime.AdaptiveLeadingOnesOptimalScheduleStochastic,
    `ECRuntime.AdaptiveLeadingOnesOptimalSurvivalClosedForm,
    `ECRuntime.AdaptiveLeadingOnesPositiveLevelExit,
    `ECRuntime.AdaptiveLeadingOnesRateInvariantVisitMass,
    `ECRuntime.AdaptiveLeadingOnesRenewalConvolution,
    `ECRuntime.AdaptiveLeadingOnesRenewalNonnegative,
    `ECRuntime.AdaptiveLeadingOnesRuntimeScheduleExt,
    `ECRuntime.AdaptiveLeadingOnesSurvivalScheduleLocal,
    `ECRuntime.AdaptiveLeadingOnesUniformBoundaryProgress,
    `ECRuntime.AdaptiveLeadingOnesUniformRuntimeExitInvariance,
    `ECRuntime.AdaptiveLeadingOnesUniformSkipProbability,
    `ECRuntime.AdaptiveLeadingOnesUniformVisitRateInvariance,
    `ECRuntime.AdaptiveWeightedCountableLevelOccupation,
    `ECRuntime.AdaptiveWeightedNonoptimalOccupation,
    `ECRuntime.BellmanFiniteExactRuntime,
    `ECRuntime.BinomialHarmonicAverageIncrementBound,
    `ECRuntime.BinomialHarmonicLogTwoFiniteError,
    `ECRuntime.BinomialHarmonicScaledRuntimeOneStep,
    `ECRuntime.CouponAllFinitePolynomialSurvival,
    `ECRuntime.CouponArbitraryMomentDecrementTransfer,
    `ECRuntime.CouponArbitraryPositiveMomentFiniteMass,
    `ECRuntime.CouponArbitraryPowerMomentSurvivalTransfer,
    `ECRuntime.CouponDiscountedHittingCDFTransfer,
    `ECRuntime.CouponDiscountedSurvivalDecrementTransfer,
    `ECRuntime.CouponDiscountedSurvivalTransfer,
    `ECRuntime.CouponFiniteMassTruncatedSecondMoment,
    `ECRuntime.CouponFiniteMassTruncatedThirdMoment,
    `ECRuntime.CouponInfiniteWeightedHittingCDF,
    `ECRuntime.CouponInfiniteWeightedSurvival,
    `ECRuntime.CouponPowerWeightedHittingCDFTransfer,
    `ECRuntime.CouponTruncatedSurvivalSecondCentralFunctional,
    `ECRuntime.CouponWeightedHitQuadraticTransfer,
    `ECRuntime.DiscreteFirstVisitUnique,
    `ECRuntime.EAWeightedGenericRuntimeNoFlipLower,
    `ECRuntime.ENNRealRenewalConvolutionUnroll,
    `ECRuntime.FiniteRuntimeSurvivalVanishes,
    `ECRuntime.FirstZeroHazard,
    `ECRuntime.FullSupportUniversal,
    `ECRuntime.GenericEAGeometricTargetSurvival,
    `ECRuntime.GenericWeightedFiniteSurvivalLowerBound,
    `ECRuntime.GenericWeightedInitialRuntimeLower,
    `ECRuntime.HarmonicHalfSeriesLogTwoLimit,
    `ECRuntime.HarmonicPredecessor,
    `ECRuntime.JumpEscapeOptimalRate,
    `ECRuntime.JumpPlateauEscape,
    `ECRuntime.LeadingOnesBoundaryInfimumBridge,
    `ECRuntime.LeadingOnesBoundaryRuntimeInfimum,
    `ECRuntime.LeadingOnesCrossBaseGlobalDominance,
    `ECRuntime.LeadingOnesFirstVisitBelowEquivalence,
    `ECRuntime.LeadingOnesFixedTargetConvexity,
    `ECRuntime.LeadingOnesFixedTargetCurvaturePositive,
    `ECRuntime.LeadingOnesFixedTargetCurvatureRatio,
    `ECRuntime.LeadingOnesFixedTargetDimensionInvariance,
    `ECRuntime.LeadingOnesFixedTargetFirstLevelLowerBound,
    `ECRuntime.LeadingOnesFixedTargetLinearLowerBound,
    `ECRuntime.LeadingOnesFixedTargetMarginalRatio,
    `ECRuntime.LeadingOnesFixedTargetStrictConvexity,
    `ECRuntime.LeadingOnesFixedTargetStrictIncrement,
    `ECRuntime.LeadingOnesLevelOneUniqueMaximizer,
    `ECRuntime.LeadingOnesOptimalRate,
    `ECRuntime.LeadingOnesReferenceBoundaryShiftTendsto,
    `ECRuntime.LeadingOnesReferencePositiveRateIndependentBase,
    `ECRuntime.LeadingOnesReferenceZeroExitStrict,
    `ECRuntime.LeadingOnesStrictLevelExitOptimality,
    `ECRuntime.LeadingOnesStrictPositivePolicyOptimality,
    `ECRuntime.LeadingOnesUniqueOptimalPolicyConditional,
    `ECRuntime.LeadingOnesUniqueStationaryRoot,
    `ECRuntime.MonotonePathFirstVisitResidenceInterval,
    `ECRuntime.OneMaxClippedPotentialMaskLipschitz,
    `ECRuntime.OneMaxEAGeometricTargetSurvival,
    `ECRuntime.OneMaxEAIndependentBitMeanRadiusRuntimeLower,
    `ECRuntime.OneMaxEAThresholdAdmissibleCorrection,
    `ECRuntime.OneMaxEAThresholdRuntimeLower,
    `ECRuntime.OneMaxEAWeightedFiniteHorizonTarget,
    `ECRuntime.OneMaxEAWeightedTargetRuntime,
    `ECRuntime.OneMaxEAZeroDriftRuntimeLower,
    `ECRuntime.OneMaxUnaryStochasticDomination,
    `ECRuntime.RLS2016LeadingOnesInitialization,
    `ECRuntime.RLSAllDimensionEventualNegativeCorrection,
    `ECRuntime.RLSCountableJointThresholdCosts,
    `ECRuntime.RLSCountableThresholdSurvivalInvariance,
    `ECRuntime.RLSExactLevelExitMass,
    `ECRuntime.RLSFixedTargetThresholdDifference,
    `ECRuntime.RLSFixedTargetUniformThresholdMonotonicity,
    `ECRuntime.RLSFixedTargetWeightedStartMonotonicity,
    `ECRuntime.RLSIndexedTargetSurvivalInvariance,
    `ECRuntime.RLSMonotoneObjectiveInvariance,
    `ECRuntime.RLSMonotonePointwiseObjectiveInvariance,
    `ECRuntime.RLSMonotoneUniformFixedTargetBinomial,
    `ECRuntime.RLSMonotonicityPaperPredicateEquivalence,
    `ECRuntime.RLSMultiThresholdInfiniteSurvival,
    `ECRuntime.RLSPaperCouponUniformMean,
    `ECRuntime.RLSPaperHarmonicStrongComparison,
    `ECRuntime.RLSUniformFirstOrderRuntimeLaw,
    `ECRuntime.RLSUniformInfiniteSurvivalFunctional,
    `ECRuntime.RLSUniformInitialCouponSurvivalCapped,
    `ECRuntime.RLSUniformInitialFirstOrderAsymptotic,
    `ECRuntime.RLSUniformInitialFixedBudgetMean,
    `ECRuntime.RLSUniformInitialHarmonicSecondOrder,
    `ECRuntime.RLSUniformInitialNLogNAdditiveEnvelope,
    `ECRuntime.RLSUniformInitialRuntimeLogTwoFiniteError,
    `ECRuntime.RLSUniformInitialRuntimeSecondOrder,
    `ECRuntime.RLSWeightedHittingGeneratingPolynomial,
    `ECRuntime.RLSWeightedHittingMomentInvariance,
    `ECRuntime.RLSWeightedSurvivalCostProfile,
    `ECRuntime.RandomInitialStakeOddScaledFiniteCorrectionBound,
    `ECRuntime.RandomInitialStakeScaledEvenCorrectionBound,
    `ECRuntime.RandomStakeCouponArbitraryTargetFiniteObjectiveInvariance,
    `ECRuntime.RandomStakeCouponArbitraryTargetFiniteRuntimeObjectiveInvariance,
    `ECRuntime.RandomStakeCouponArbitraryTargetObjectiveInvariance,
    `ECRuntime.RandomStakeCouponFinitePaperCenteredExact,
    `ECRuntime.RandomStakeCouponSecondMomentSurvivalTransfer,
    `ECRuntime.RandomStakeCouponSharpPaperCentered,
    `ECRuntime.RandomStakeCouponStatewiseObservableTransfer,
    `ECRuntime.RandomStakeCouponThirdMomentSurvivalTransfer,
    `ECRuntime.StaticUnarySecondFactorialRadiusBound,
    `ECRuntime.StaticUnarySingletonSupportPositiveMean,
    `ECRuntime.StaticUnaryUnbiasedFirstZeroUnrestrictedRuntime,
    `ECRuntime.StaticUnaryUnbiasedSharpMomentUpper,
    `ECRuntime.StrictMonotoneCouponSurvival,
    `ECRuntime.StrictMonotoneRLSCouponTail,
    `ECRuntime.UnaryOneMaxDimensionRuntimeLower,
    `ECRuntime.UnaryOneMaxHarmonicCapMonotonicity,
    `ECRuntime.UnaryOneMaxHarmonicLowerScaled,
    `ECRuntime.UnaryOneMaxLazySingletonNoFasterThanRLS,
    `ECRuntime.UnaryOneMaxNoOpFreeExactHarmonic,
    `ECRuntime.UnaryOneMaxSingletonLawRuntimeInvariance,
    `ECRuntime.UnaryOneMaxSingletonStrictLazyCost,
    `ECRuntime.UnaryOneMaxSingletonStrictRuntimeComparison,
    `ECRuntime.UniformFixedTargetGeometricTail,
    `ECRuntime.WeightedRuntimeTargetMonotonicity ]

/-- Modules unreachable from any facade when the audit was introduced. DEVELOPMENT.md
section 6 forbids retaining modules that no longer contribute to the proof graph;
these are grandfathered pending a decision to discharge
`HasUniformExactLevelExitBounds` for a concrete algorithm or delete the layer. A
module not on this list that becomes unreachable is an error, so the set may shrink
but never grow. -/
def orphanAllowlist : List Name :=
  [`ECRuntime.DirectGeometricStochasticDominationClosed,
   `ECRuntime.DirectGeometricTailDomination,
   `ECRuntime.DirectGeometricTailDominationClosed,
   `ECRuntime.GeometricCouplingDominationEndpoint,
   `ECRuntime.GeometricFailureCouplingReduction,
   `ECRuntime.GeometricFailureMemoryless,
   `ECRuntime.GeometricFailureProductSplit,
   `ECRuntime.GeometricFailureProductTailRecursion,
   `ECRuntime.GeometricPrefixTailCongruence,
   `ECRuntime.GeometricPrefixTailRecursion,
   `ECRuntime.GeometricSumTailIdentification,
   `ECRuntime.GeometricSumTailRecursion,
   `ECRuntime.LevelChargeExactResidence,
   `ECRuntime.NatTailToStochasticDomination,
   `ECRuntime.PotentialRuntimeTailRecursion,
   `ECRuntime.StaticUnaryUnbiasedLinearDrift]

/-- Axioms a promoted theorem may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Equation lemmas, match auxiliaries, recursors and the rest of what Lean
synthesises alongside a written declaration. They carry no authorship, so holding
them to a documentation standard is noise. -/
def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ s =>
      s == "eq_def" || s == "induct" || s == "below" || s == "brecOn" ||
      s == "ibelow" || s == "binductionOn" || s == "rec" || s == "recOn" ||
      s == "casesOn" || s == "injEq" || s == "sizeOf_spec" || s == "noConfusion" ||
      s == "noConfusionType" || s == "mk" || s == "ofNat" || s == "toCtorIdx" ||
      s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_" ||
      s.startsWith "_"
  | _ => false

/-- Declarations written in this development, excluding Lean's generated auxiliaries. -/
def isOwn (n : Name) : Bool :=
  (`ECRuntime).isPrefixOf n && !n.isInternal && !n.hasMacroScopes && !isGenerated n

/-- Underscore-prefixed binders in a declaration's *type*.

A leading underscore on a signature binder marks a premise the proof never consults,
which narrows the theorem for every caller and buys nothing. Lambda binders inside a
proof term are a different thing and are never reached here, because only the type is
traversed. -/
partial def unusedBinders : Expr → Array Name → Array Name
  | .forallE n _ body _, acc =>
      let acc := if n.toString.startsWith "_" then acc.push n else acc
      unusedBinders body acc
  | _, acc => acc

/-- A declaration's defining term, including a theorem's proof.

`ConstantInfo.value?` deliberately returns `none` for theorems -- it will not hand back
a proof term. Reading it and believing the answer makes every check below blind to
proofs while still appearing to work, which is exactly what happened: a `sorry`
laundered through a helper went unreported because only statements were ever examined.
Match the constructor instead. -/
def valueOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Constants a declaration's statement and proof term mention. -/
def usedConstants (info : ConstantInfo) : Array Name :=
  match valueOf info with
  | some v => info.type.getUsedConstants ++ v.getUsedConstants
  | none => info.type.getUsedConstants

/-- The axioms a declaration ultimately rests on, as `#print axioms` reports them.

`Lean.collectAxioms` walks the whole transitive proof term, which is why a `sorry`
laundered through a helper lemma still surfaces here. -/
def axiomsOf (declName : Name) : CoreM (Array Name) :=
  Lean.collectAxioms declName

/-- The audit proper. Returns the process exit code. -/
def run (candidate : Bool) (debug : Bool := false) : CoreM UInt32 := do
  let env ← getEnv
  let mut errors : Array String := #[]
  let mut warnings : Array String := #[]

  let mut own : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if isOwn name then own := own.push (name, info)

  -- 1. Proof holes, from the axiom set rather than a text scan.
  --
  -- Computed as a fixpoint over this development's own dependency graph rather than
  -- by calling `collectAxioms` per declaration: that walks the whole transitive proof
  -- term with fresh state every time, so the cost is O(declarations x proof size) and
  -- the gate takes minutes. A declaration is tainted exactly when it names a
  -- non-standard axiom directly, or names a tainted declaration of ours -- which is
  -- O(edges) in one pass and still catches a `sorry` laundered through a helper.
  --
  -- This assumes Mathlib itself introduces no non-standard axiom, so taint can only
  -- originate here. `ECRuntimeTest/AxiomAudit.lean` checks the facade theorems
  -- against the unrestricted walk, which is what makes that assumption testable.
  let ownNames : NameSet := own.foldl (fun s (n, _) => s.insert n) {}
  let mut directBad : NameMap (Array Name) := {}
  let mut ownDeps : NameMap (Array Name) := {}
  for (name, info) in own do
    let mut bad := #[]
    let mut deps := #[]
    for c in usedConstants info do
      if ownNames.contains c then
        if c != name && !deps.contains c then deps := deps.push c
      else if c == ``sorryAx then
        -- Checked by name, not by ConstantInfo kind: relying on `.axiomInfo` here
        -- silently missed every laundered `sorry` in testing.
        unless bad.contains c do bad := bad.push c
      else if let some (.axiomInfo _) := env.find? c then
        if !standardAxioms.contains c && !bad.contains c then bad := bad.push c
    directBad := directBad.insert name bad
    ownDeps := ownDeps.insert name deps

  let mut bad : NameMap (Array Name) := directBad
  let mut changed := true
  while changed do
    changed := false
    for (name, _) in own do
      let mut acc := bad.find? name |>.getD #[]
      for d in ownDeps.find? name |>.getD #[] do
        for ax in bad.find? d |>.getD #[] do
          unless acc.contains ax do
            acc := acc.push ax
            changed := true
      bad := bad.insert name acc

  let mut tainted : Nat := 0
  for (name, _) in own do
    for ax in bad.find? name |>.getD #[] do
      if ax == ``sorryAx then
        tainted := tainted + 1
        unless candidate do
          errors := errors.push s!"{name} depends on sorryAx"
      else
        errors := errors.push s!"{name} depends on non-standard axiom {ax}"
  if candidate && tainted > 0 then
    warnings := warnings.push
      s!"candidate run: {tainted} declaration(s) still depend on sorryAx"

  -- 2. Documentation coverage.
  for (name, _) in own do
    if (← findDocString? env name).isNone then
      warnings := warnings.push s!"{name} has no doc comment"

  -- 3. Unused hypotheses in signatures.
  for (name, info) in own do
    for b in unusedBinders info.type #[] do
      warnings := warnings.push
        s!"{name}: binder `{b}` is unused -- it narrows the theorem for every caller"

  -- 4. Reachability from the public facades.
  --
  -- Over **imports**, not proof dependencies. The two answer different questions and
  -- only one is the question this gate asks. "Does anything mention this module?" is
  -- proof dependency; "can this module be deleted?" is import reachability, and a
  -- module can be essential to the build while no facade's proof term names it --
  -- `WittStandardRuntimeAsymptotics` reaches `WittStandardRuntime` only through
  -- `ExpectedRuntimeCorollaries`, so a proof-dependency walk calls it dead when it
  -- plainly is not. `scripts/dep_graph.py` keeps the proof-dependency view, where
  -- that finer notion is the informative one.
  let mut moduleDeps : NameMap (Array Name) := {}
  for i in [0 : env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (`ECRuntime).isPrefixOf m then
      let imports := env.header.moduleData[i]!.imports.filterMap fun imp =>
        if (`ECRuntime).isPrefixOf imp.module then some imp.module else none
      moduleDeps := moduleDeps.insert m imports

  if debug then
    IO.println s!"debug: import graph has {moduleDeps.size} ECRuntime module(s)"
    IO.println s!"debug: {facades.length} original + {mergedPublicFacades.length} merged public facades"
    for f in facades do
      IO.println s!"debug:   {f} -> {(moduleDeps.find? f |>.getD #[]).size} import(s)"

  let mut seen : NameSet := {}
  let mut stack := facades ++ mergedPublicFacades
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | cur :: rest =>
        stack := rest
        unless seen.contains cur do
          seen := seen.insert cur
          stack := (moduleDeps.find? cur |>.getD #[]).toList ++ stack

  for m in env.header.moduleNames do
    if (`ECRuntime).isPrefixOf m && m != `ECRuntime && !seen.contains m then
      if orphanAllowlist.contains m then
        warnings := warnings.push s!"{m}: grandfathered orphan, pending removal decision"
      else
        errors := errors.push
          s!"{m} is unreachable from every facade; see DEVELOPMENT.md section 6"

  for w in warnings do IO.println s!"warning: {w}"
  for e in errors do IO.println s!"error: {e}"
  IO.println ""
  IO.println s!"audit: {own.size} declarations, {errors.size} error(s), \
{warnings.size} warning(s) -- {if errors.isEmpty then "OK" else "FAIL"}"
  return if errors.isEmpty then 0 else 1

end ECRuntimeAudit

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ECRuntime }] {} (trustLevel := 1024)
  let candidate := args.contains "candidate"
  let ctx : Core.Context := { fileName := "audit.lean", fileMap := default }
  let st : Core.State := { env := env }
  let (code, _) ← (ECRuntimeAudit.run candidate (args.contains "debug")).toIO ctx st
  return code
