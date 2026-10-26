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
but never grow.

The list held sixteen modules until the 547-module merge; fifteen became reachable from
`mergedPublicFacades` and were removed. -/
def orphanAllowlist : List Name :=
  [`ECRuntime.LevelChargeExactResidence]

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

/-- The audit proper. Returns `(errors, warnings, declaration count)`.

Separated from reporting so that the text gate and the JSON state are two views of one
computation. Deriving them independently would reintroduce exactly the duplication this
file exists to remove. -/
def collect (candidate : Bool) (debug : Bool := false) :
    CoreM (Array String × Array String × Nat) := do
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
  -- plainly is not. The `graph` view below keeps the proof-dependency picture, where
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

  return (errors, warnings, own.size)

/-- Report the findings and return the process exit code. -/
def run (candidate : Bool) (debug : Bool := false) : CoreM UInt32 := do
  let (errors, warnings, declCount) ← collect candidate debug
  for w in warnings do IO.println s!"warning: {w}"
  for e in errors do IO.println s!"error: {e}"
  IO.println ""
  IO.println s!"audit: {declCount} declarations, {errors.size} error(s), {warnings.size} warning(s) -- {if errors.isEmpty then "OK" else "FAIL"}"
  return if errors.isEmpty then 0 else 1


/-! ## Module dependency graph and machine-readable state

Absorbs the former `scripts/dep_extract.lean`, `dep_graph.py`, `dep_graph.ps1` and
`state_report.py`. Those carried their own copies of the facade list and the orphan
allowlist, kept in sync by hand; `dep_graph.ps1` was already stale. Here the lists
declared above are the only copies, and the environment is walked once, not twice.
-/

namespace Graph

/-- `ECRuntime.BitString` becomes `BitString`. -/
def shortName (m : Name) : String :=
  let s := m.toString
  if s.startsWith "ECRuntime." then (s.drop "ECRuntime.".length).toString else s

/-- Architectural family of a module. First match wins; these are the prefixes the
former `dep_graph` scripts matched by regular expression. -/
def familyOf (m : String) : String :=
  if m.startsWith "StaticUnary" then "Static unary-unbiased"
  else if m.startsWith "WittMutation" then "Witt scaled rate c/n"
  else if m.startsWith "WittStandard" then "Witt standard rate 1/n"
  else if m.startsWith "LeadingOnes" || m.startsWith "AdaptiveLeadingOnes" then "LeadingOnes"
  else if ["RLS", "Coupon", "RandomStakeCoupon", "RandomInitialStake",
           "StrictMonotone"].any (m.startsWith ·) then
    "RLS & coupon collector"
  else if m == "BitString" || m == "Objective" || m == "Mutation" || m == "Transition" then
    "Foundations"
  else if ["FiniteTrajectory", "TransitionKernel", "FiniteMarginal", "PrefixMarginal",
           "Trajectory", "UnrestrictedRuntime", "HittingTime"].any (m.startsWith ·) then
    "Trajectory semantics"
  else if ["Linear", "OneMax", "UnaryOneMax", "Jump", "AsymptoticRegime", "MutationRate",
           "ExpectedRuntime"].any (m.startsWith ·) then
    "Objectives & asymptotics"
  else "Generic runtime theory"

/-- Mermaid shares one identifier space between nodes and subgraphs, so the family
`LeadingOnes` would collide with the module of that name. They get separate prefixes. -/
def sanitize (s : String) : String :=
  s.map fun c => if c.isAlphanum || c == '_' then c else '_'

def nodeId (s : String) : String := "n_" ++ sanitize s

def subgraphId (s : String) : String := "sg_" ++ sanitize s

/-- Everything the graph and state views need, read once. -/
structure Data where
  /-- Short module name of each own declaration. -/
  declModule : Std.HashMap String String
  /-- Cross-module proof dependencies, deduplicated. An edge means a statement or proof
  term actually mentions the target, not merely that the module was imported. -/
  moduleEdges : Array (String × String)
  /-- Every module on disk, including re-export facades that declare nothing. -/
  allModules : Array String
  /-- The `import ECRuntime.X` lines of each module. -/
  moduleImports : Std.HashMap String (Array String)
  /-- Own declarations, excluding Lean's generated auxiliaries. -/
  declCount : Nat
  /-- Modules declaring at least one constant. -/
  declaring : Std.HashSet String
  /-- Declaration-level proof dependencies, for the single-theorem view. -/
  declEdges : Array (String × String)

/-- Walk the environment once, then read the module sources. -/
def gather : CoreM Data := do
  let env ← getEnv
  let mut declModule : Std.HashMap String String := .emptyWithCapacity
  let mut declaring : Std.HashSet String := .emptyWithCapacity
  let mut uses : Array (String × Array Name) := #[]
  let mut declCount := 0
  for (name, info) in env.constants.toList do
    unless isOwn name do continue
    let m := match env.getModuleFor? name with
      | some mm => shortName mm
      | none => "unknown"
    declModule := declModule.insert name.toString m
    declaring := declaring.insert m
    declCount := declCount + 1
    uses := uses.push (name.toString, usedConstants info)
  let mut seen : Std.HashSet String := .emptyWithCapacity
  let mut moduleEdges : Array (String × String) := #[]
  let mut declEdges : Array (String × String) := #[]
  for (src, consts) in uses do
    match declModule[src]? with
    | none => pure ()
    | some a =>
      let mut seenC : Std.HashSet String := .emptyWithCapacity
      for c in consts do
        if isOwn c then
          match declModule[c.toString]? with
          | none => pure ()
          | some b =>
            let cs := c.toString
            if cs != src then
              unless seenC.contains cs do
                seenC := seenC.insert cs
                declEdges := declEdges.push (src, cs)
            if a != b then
              let k := a ++ "\t" ++ b
              unless seen.contains k do
                seen := seen.insert k
                moduleEdges := moduleEdges.push (a, b)
  let entries ← System.FilePath.readDir "ECRuntime"
  let mut allModules : Array String := #[]
  let mut moduleImports : Std.HashMap String (Array String) := .emptyWithCapacity
  for e in entries do
    let fn := e.fileName
    unless fn.endsWith ".lean" do continue
    let base := (fn.dropEnd 5).toString
    allModules := allModules.push base
    let txt ← IO.FS.readFile e.path
    let imps := (txt.splitOn "\n").filterMap fun l =>
      if l.startsWith "import ECRuntime." then
        some ((l.drop 17).trimAscii.toString)
      else
        none
    moduleImports := moduleImports.insert base imps.toArray
  return { declModule := declModule, moduleEdges := moduleEdges,
           allModules := allModules.qsort (· < ·), moduleImports := moduleImports,
           declCount := declCount, declaring := declaring,
           declEdges := declEdges }

/-- Successor lists of an edge set. -/
def succMap (edges : Array (String × String)) : Std.HashMap String (Array String) :=
  edges.foldl (init := .emptyWithCapacity) fun m e =>
    m.insert e.1 ((m.getD e.1 #[]).push e.2)

/-- Is `b` reachable from `a` without using the direct edge `a -> b`? -/
partial def canReachIndirectly (succ : Std.HashMap String (Array String))
    (a b : String) : Bool :=
  Id.run do
    let mut stack : Array String := #[a]
    let mut seen : Std.HashSet String := (Std.HashSet.emptyWithCapacity).insert a
    while stack.size > 0 do
      let cur := stack.back!
      stack := stack.pop
      for nxt in succ.getD cur #[] do
        if cur == a && nxt == b then
          continue
        if nxt == b then
          return true
        unless seen.contains nxt do
          seen := seen.insert nxt
          stack := stack.push nxt
    return false

/-- Drop every edge already implied by a longer path. -/
def transitiveReduction (edges : Array (String × String)) : Array (String × String) :=
  let succ := succMap edges
  edges.filter fun e => !canReachIndirectly succ e.1 e.2

def header (title : String) (extra : List String) : List String :=
  ["%% " ++ title,
   "%% Generated by scripts/audit.lean from real proof dependencies.",
   "%% An edge means a proof or statement mentions the target."] ++ extra ++
  ["", "graph BT"]

def styles : List String :=
  ["",
   "  classDef facade stroke-width:3px,stroke:#1d7a55,fill:#e7f4ee,color:#12291f;",
   "  classDef orphan stroke-dasharray:4 3,stroke:#96620f,fill:#fbf1de,color:#2a2113;"]

/-- Architecture at a glance: one node per family, edge labels counting the module
dependencies that cross a family boundary. -/
def renderFamily (d : Data) : String :=
  Id.run do
    let mut famEdges : Std.HashMap String Nat := .emptyWithCapacity
    for e in d.moduleEdges do
      let fa := familyOf e.1
      let fb := familyOf e.2
      if fa != fb then
        let k := fa ++ "\t" ++ fb
        famEdges := famEdges.insert k (famEdges.getD k 0 + 1)
    let mut counts : Std.HashMap String Nat := .emptyWithCapacity
    for m in d.allModules do
      let f := familyOf m
      counts := counts.insert f (counts.getD f 0 + 1)
    let fams := (counts.toList.map (fun p => p.1)).toArray.qsort (· < ·)
    let mut out := header "ECRuntime proof architecture, by family" []
    for f in fams do
      let label := f ++ "<br/><small>" ++ toString (counts.getD f 0) ++ " modules</small>"
      out := out ++ ["  " ++ nodeId f ++ "[\"" ++ label ++ "\"]"]
    out := out ++ [""]
    let ranked := famEdges.toList.toArray.qsort fun x y =>
      if x.2 == y.2 then x.1 < y.1 else x.2 > y.2
    for p in ranked do
      match p.1.splitOn "\t" with
      | [a, b] => out := out ++ ["  " ++ nodeId a ++ " -->|" ++ toString p.2 ++ "| " ++ nodeId b]
      | _ => pure ()
    return "\n".intercalate (out ++ styles)

/-- Every module, grouped into family subgraphs, transitively reduced by default.
A re-export module declares nothing and so has no proof edges; its import edges are
drawn dashed instead, which is the only place an import graph is used at all. -/
def renderModules (d : Data) (reduce : Bool) : String :=
  Id.run do
    let medges := if reduce then transitiveReduction d.moduleEdges else d.moduleEdges
    let reexport := d.allModules.filter fun m => !d.declaring.contains m
    let mut byFamily : Std.HashMap String (Array String) := .emptyWithCapacity
    for m in d.allModules do
      let f := familyOf m
      byFamily := byFamily.insert f ((byFamily.getD f #[]).push m)
    let fams := (byFamily.toList.map (fun p => p.1)).toArray.qsort (· < ·)
    let mut out := header "ECRuntime module dependencies (transitively reduced)"
      ["%% Dashed edge: re-export only -- the module declares nothing itself."]
    for f in fams do
      out := out ++ ["  subgraph " ++ subgraphId f ++ "[\"" ++ f ++ "\"]"]
      for m in byFamily.getD f #[] do
        out := out ++ ["    " ++ nodeId m ++ "[\"" ++ m ++ "\"]"]
      out := out ++ ["  end"]
    out := out ++ [""]
    let sorted := medges.qsort fun x y => if x.1 == y.1 then x.2 < y.2 else x.1 < y.1
    for e in sorted do
      out := out ++ ["  " ++ nodeId e.1 ++ " --> " ++ nodeId e.2]
    for m in reexport do
      for dep in d.moduleImports.getD m #[] do
        if d.allModules.contains dep then
          out := out ++ ["  " ++ nodeId m ++ " -.-> " ++ nodeId dep]
    out := out ++ styles
    let fac := ((facades ++ mergedPublicFacades).map shortName).toArray.filter
      d.allModules.contains
    let orp := (orphanAllowlist.map shortName).toArray.filter d.allModules.contains
    if fac.size > 0 then
      let ids := ",".intercalate ((fac.qsort (· < ·)).map nodeId).toList
      out := out ++ ["  class " ++ ids ++ " facade;"]
    if orp.size > 0 then
      let ids := ",".intercalate ((orp.qsort (· < ·)).map nodeId).toList
      out := out ++ ["  class " ++ ids ++ " orphan;"]
    return "\n".intercalate out

/-- Deduplicate a sorted array. -/
def dedupSorted (a : Array String) : Array String :=
  a.foldl (init := #[]) fun acc x => if acc.isEmpty || acc.back! != x then acc.push x else acc

/-- One module's direct proof neighbourhood: what it rests on, and what rests on it. -/
def renderNeighbourhood (d : Data) (target : String) : Option String :=
  if !d.allModules.contains target then none
  else Id.run do
    let mut ups : Array String := #[]
    let mut downs : Array String := #[]
    for e in d.moduleEdges do
      if e.2 == target then ups := ups.push e.1
      if e.1 == target then downs := downs.push e.2
    let mut out := header (target ++ ": direct proof dependencies") []
    out := out ++ ["  " ++ nodeId target ++ "[\"" ++ target ++ "\"]"]
    for m in dedupSorted (ups.qsort (· < ·)) do
      out := out ++ ["  " ++ nodeId m ++ "[\"" ++ m ++ "\"]",
                     "  " ++ nodeId m ++ " --> " ++ nodeId target]
    for m in dedupSorted (downs.qsort (· < ·)) do
      out := out ++ ["  " ++ nodeId m ++ "[\"" ++ m ++ "\"]",
                     "  " ++ nodeId target ++ " --> " ++ nodeId m]
    out := out ++ styles ++ ["  class " ++ nodeId target ++ " facade;"]
    return some ("\n".intercalate out)

/-- Resolve a theorem argument to a full declaration name, accepting a unique suffix. -/
def resolveDecl (d : Data) (root : String) : Option String :=
  let full := if root.startsWith "ECRuntime." then root else "ECRuntime." ++ root
  if d.declModule.contains full then some full
  else
    match (d.declModule.toList.map (fun p => p.1)).filter (fun k => k.endsWith ("." ++ root)) with
    | [c] => some c
    | _ => none

/-- One theorem's proof-dependency tree, breadth-first to a fixed depth. -/
def renderTheorem (d : Data) (full : String) (maxDepth : Nat) : String :=
  Id.run do
    let succ := succMap d.declEdges
    let mut level : Std.HashMap String Nat := (Std.HashMap.emptyWithCapacity).insert full 0
    let mut order : Array String := #[full]
    let mut frontier : Array String := #[full]
    for dep in [1 : maxDepth + 1] do
      let mut next : Array String := #[]
      for cur in frontier do
        for t in dedupSorted ((succ.getD cur #[]).qsort (· < ·)) do
          unless level.contains t do
            level := level.insert t dep
            order := order.push t
            next := next.push t
      frontier := next
    let short (n : String) : String :=
      if n.startsWith "ECRuntime." then (n.drop 10).toString else n
    let mut out := header (short full ++ " : proof dependencies, depth " ++ toString maxDepth) []
    for n in order do
      let label := short n ++ "<br/><small>" ++ d.declModule.getD n "?" ++ "</small>"
      out := out ++ ["  " ++ nodeId n ++ "[\"" ++ label ++ "\"]"]
    out := out ++ [""]
    for a in order do
      for b in dedupSorted ((succ.getD a #[]).qsort (· < ·)) do
        if level.contains b then
          out := out ++ ["  " ++ nodeId a ++ " --> " ++ nodeId b]
    out := out ++ styles ++ ["  class " ++ nodeId full ++ " facade;"]
    return "\n".intercalate out

/-- Imports removable without losing a proof dependency.

An import is **not** redundant merely because nothing in it is mentioned: it may be the
only route to a module that is. `ExpectedRuntimeCorollaries` mentions nothing from
`LinearRuntime`, yet dropping that import breaks the build, because it is how `OneMax`
arrives. So an import is removable only when every module the importer actually depends
on stays reachable through the imports that remain. Candidates, not a verdict: an import
can also carry notation or a scoped instance that no proof term mentions. -/
def renderRedundantImports (d : Data) : String :=
  Id.run do
    let closure (roots : Array String) : Std.HashSet String := Id.run do
      let mut seen : Std.HashSet String := .emptyWithCapacity
      let mut stack := roots
      while stack.size > 0 do
        let cur := stack.back!
        stack := stack.pop
        unless seen.contains cur do
          seen := seen.insert cur
          for dep in d.moduleImports.getD cur #[] do
            stack := stack.push dep
      return seen
    let mut lines : Array String := #[]
    let mut total := 0
    for m in d.allModules do
      let needed := dedupSorted
        ((d.moduleEdges.filter (fun e => e.1 == m) |>.map (fun e => e.2)).qsort (· < ·))
      let imps := d.moduleImports.getD m #[]
      let mut removable : Array String := #[]
      for cand in imps do
        let rest := imps.filter (fun i => i != cand)
        let reach := closure rest
        if needed.all reach.contains then removable := removable.push cand
      total := total + removable.size
      if removable.size > 0 then
        lines := lines.push (m ++ ":  (depends on " ++ toString needed.size ++ " module(s))")
        for dep in removable do
          lines := lines.push ("    import ECRuntime." ++ dep)
    let head := #[
      toString total ++ " import(s) are individually removable: every module the importer",
      "actually depends on stays reachable without them. Candidates, not a verdict -- an",
      "import can also carry notation or a scoped instance that no proof term mentions.",
      "Elaborate before deleting.",
      ""]
    return "\n".intercalate (head ++ lines).toList

end Graph

/-- First value after `flag` in `args`, if present. -/
def optArg (args : List String) (flag : String) : Option String :=
  match args.dropWhile (fun a => a != flag) with
  | _ :: v :: _ => some v
  | _ => none

/-- Emit, as JSON, the semantic facts this audit owns: the facade and orphan lists, the
counts, and every finding. The text-munging half of the former `state_report.py` --- line
counts, toolchain version strings, `frontier.toml` parsing --- is deliberately not
reproduced in Lean, because none of it is a fact about the proof. -/
def runJson (args : List String) : CoreM UInt32 := do
  let (errors, warnings, declCount) ← collect (args.contains "candidate")
  let d ← Graph.gather
  let strs (a : Array String) : Json := Json.arr (a.map Json.str)
  let names (l : List Name) : Json := strs ((l.map toString).toArray)
  let j := Json.mkObj [
    ("declarations", Json.num declCount),
    ("modules", Json.num d.allModules.size),
    ("module_edges", Json.num d.moduleEdges.size),
    ("error_count", Json.num errors.size),
    ("warning_count", Json.num warnings.size),
    ("clean", Json.bool errors.isEmpty),
    ("facades", names facades),
    ("merged_public_facades", names mergedPublicFacades),
    ("orphan_allowlist", names orphanAllowlist),
    ("errors", strs errors),
    ("warnings", strs warnings)]
  match optArg args "--output" with
  | some path =>
      IO.FS.writeFile path (j.pretty ++ "
")
      IO.println s!"wrote {path}"
  | none => IO.println j.pretty
  return if errors.isEmpty then 0 else 1

/-- Emit a Mermaid view, or the removable-import report.

`--level family|module`, `--module <name>`, `--theorem <name> --depth N`,
`--redundant-imports`, `--output <path>`, `--no-reduce`.

`--all --outdir <dir>` regenerates the two general views in a single environment walk,
which is what the verification runner invokes. The `frontier-*` views are not included:
they are snapshots of one named module and one named theorem, so what they should point
at changes when the frontier moves, and regenerating them silently against a stale
target would be worse than leaving them explicit. -/
def runGraph (args : List String) : CoreM UInt32 := do
  let d ← Graph.gather
  let emit (text : String) : CoreM UInt32 := do
    match optArg args "--output" with
    | some path =>
        IO.FS.writeFile path (text ++ "
")
        IO.println s!"wrote {path}"
    | none => IO.println text
    return 0
  if args.contains "--all" then
    let dir := (optArg args "--outdir").getD "docs/current/graphs"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir ++ "/architecture.mmd") (Graph.renderFamily d ++ "
")
    IO.FS.writeFile (dir ++ "/modules.mmd") (Graph.renderModules d true ++ "
")
    IO.println s!"wrote {dir}/architecture.mmd, {dir}/modules.mmd ({d.allModules.size} modules, {d.moduleEdges.size} edges)"
    return 0
  if args.contains "--redundant-imports" then
    return (← emit (Graph.renderRedundantImports d))
  match optArg args "--module" with
  | some m =>
      match Graph.renderNeighbourhood d m with
      | some t => return (← emit t)
      | none => IO.println s!"error: no module named {m}"; return 2
  | none =>
  match optArg args "--theorem" with
  | some t =>
      match Graph.resolveDecl d t with
      | some full =>
          let depth := ((optArg args "--depth").bind String.toNat?).getD 2
          return (← emit (Graph.renderTheorem d full depth))
      | none => IO.println s!"error: no unique declaration {t}"; return 2
  | none =>
  let level := (optArg args "--level").getD "family"
  emit (if level == "module" then Graph.renderModules d (!args.contains "--no-reduce")
        else Graph.renderFamily d)

end ECRuntimeAudit

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ECRuntime }] {} (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "audit.lean", fileMap := default }
  let st : Core.State := { env := env }
  if args.contains "graph" then
    let (code, _) ← (ECRuntimeAudit.runGraph args).toIO ctx st
    return code
  if args.contains "json" then
    let (code, _) ← (ECRuntimeAudit.runJson args).toIO ctx st
    return code
  let candidate := args.contains "candidate"
  let (code, _) ← (ECRuntimeAudit.run candidate (args.contains "debug")).toIO ctx st
  return code
