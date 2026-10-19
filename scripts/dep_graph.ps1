<#
.SYNOPSIS
  Render the ECRuntime proof-dependency network as Mermaid.

.DESCRIPTION
  Input is the data produced by scripts\dep_extract.lean, which walks the compiled
  environment. An edge means a proof or statement actually mentions the target, not
  merely that its module was imported.

  Refresh the data first:
      lake env lean scripts\dep_extract.lean

.PARAMETER Level
  family (architecture at a glance) or module (all modules, transitively reduced).

.PARAMETER Module
  One module's direct neighbourhood.

.PARAMETER Theorem
  One theorem's dependency tree.

.PARAMETER RedundantImports
  Imports removable without losing a proof dependency. Candidates, not a verdict.

.EXAMPLE
  pwsh -File scripts\dep_graph.ps1 -Level family -Output docs\graphs\architecture.mmd
#>
[CmdletBinding()]
param(
    [ValidateSet('family', 'module')][string]$Level = 'family',
    [string]$Module,
    [string]$Theorem,
    [int]$Depth = 2,
    [switch]$NoReduce,
    [switch]$RedundantImports,
    [string]$Output
)

$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
$declsPath = Join-Path $repo '.verify\decls.tsv'
$depsPath  = Join-Path $repo '.verify\deps.tsv'

if (-not (Test-Path $declsPath) -or -not (Test-Path $depsPath)) {
    Write-Error 'run `lake env lean scripts\dep_extract.lean` first'
    exit 2
}

# Modules that constitute the public API; kept in step with scripts\audit.lean.
$Facades = @(
    'LeadingOnesMainResults', 'WittStandardRuntimeAsymptotics', 'WittStandardRuntimeTail',
    'WittMutationLogThreeRuntime', 'WittMutationSharpRuntimeAsymptotics',
    'StaticUnaryUnbiasedCorrectedLeftGain'
)
$OrphanAllowlist = @(
    'DirectGeometricStochasticDominationClosed', 'DirectGeometricTailDomination',
    'DirectGeometricTailDominationClosed', 'GeometricCouplingDominationEndpoint',
    'GeometricFailureCouplingReduction', 'GeometricFailureMemoryless',
    'GeometricFailureProductSplit', 'GeometricFailureProductTailRecursion',
    'GeometricPrefixTailCongruence', 'GeometricPrefixTailRecursion',
    'GeometricSumTailIdentification', 'GeometricSumTailRecursion',
    'LevelChargeExactResidence', 'NatTailToStochasticDomination',
    'PotentialRuntimeTailRecursion', 'StaticUnaryUnbiasedLinearDrift'
)

# Lean synthesises equation lemmas and match auxiliaries alongside written
# declarations. They carry no architectural meaning.
$Generated = '\.(eq_\d+|eq_def|match_\d+|proof_\d+|induct|below|brecOn|ibelow|binductionOn|noConfusion\w*|rec|recOn|casesOn|sizeOf_spec|injEq)$'

# First match wins; order matters.
$Families = @(
    @{ P = '^StaticUnaryUnbiased'; F = 'Static unary-unbiased' },
    @{ P = '^WittMutation';        F = 'Witt scaled rate c/n' },
    @{ P = '^WittStandard';        F = 'Witt standard rate 1/n' },
    @{ P = '^LeadingOnes';         F = 'LeadingOnes' },
    @{ P = '^(BitString|Objective|Mutation|Transition)$'; F = 'Foundations' },
    @{ P = '^(FiniteTrajectory|TransitionKernel|FiniteMarginal|PrefixMarginal|Trajectory|UnrestrictedRuntime|HittingTime)'; F = 'Trajectory semantics' },
    @{ P = '^(Linear|OneMax|AsymptoticRegime|MutationRate|ExpectedRuntime)'; F = 'Objectives & asymptotics' }
)

function Get-Family([string]$m) {
    foreach ($f in $Families) { if ($m -match $f.P) { return $f.F } }
    return 'Generic runtime theory'
}

function Get-NodeId([string]$n)     { 'n_' + ($n -replace '[^A-Za-z0-9_]', '_') }
# Subgraph identifiers live in their own namespace: Mermaid shares one identifier
# space with nodes, and the family "LeadingOnes" collides with the module of that name.
function Get-SubgraphId([string]$n) { 'sg_' + ($n -replace '[^A-Za-z0-9_]', '_') }

# --- load ---------------------------------------------------------------------
$declModule = @{}
foreach ($line in [IO.File]::ReadAllLines($declsPath)) {
    if (-not $line) { continue }
    $p = $line -split "`t"
    if ($p[0] -match $Generated) { continue }
    $declModule[$p[0]] = $p[1] -replace '^ECRuntime\.', ''
}

$edges = [System.Collections.Generic.List[string[]]]::new()
foreach ($line in [IO.File]::ReadAllLines($depsPath)) {
    if (-not $line) { continue }
    $p = $line -split "`t"
    if ($declModule.ContainsKey($p[0]) -and $declModule.ContainsKey($p[1])) { $edges.Add($p) }
}

# Every module on disk, including pure re-export facades that declare nothing and so
# never appear in the declaration table.
$allModules = Get-ChildItem (Join-Path $repo 'ECRuntime') -Filter *.lean -File |
              ForEach-Object { $_.BaseName }

$moduleImports = @{}
foreach ($f in Get-ChildItem (Join-Path $repo 'ECRuntime') -Filter *.lean -File) {
    $moduleImports[$f.BaseName] = @(
        Select-String -LiteralPath $f.FullName -Pattern '^import ECRuntime\.([A-Za-z0-9_]+)' |
        ForEach-Object { $_.Matches[0].Groups[1].Value }
    )
}

$moduleEdges = New-Object 'System.Collections.Generic.HashSet[string]'
foreach ($e in $edges) {
    $a = $declModule[$e[0]]; $b = $declModule[$e[1]]
    if ($a -ne $b) { [void]$moduleEdges.Add("$a`t$b") }
}

function Get-Successors($edgeSet) {
    $succ = @{}
    foreach ($e in $edgeSet) {
        $p = $e -split "`t"
        if (-not $succ.ContainsKey($p[0])) { $succ[$p[0]] = [System.Collections.Generic.List[string]]::new() }
        $succ[$p[0]].Add($p[1])
    }
    return $succ
}

function Get-TransitiveReduction($edgeSet) {
    $succ = Get-Successors $edgeSet
    $keep = New-Object 'System.Collections.Generic.HashSet[string]'
    foreach ($e in $edgeSet) {
        $p = $e -split "`t"
        $a = $p[0]; $b = $p[1]
        $stack = [System.Collections.Generic.Stack[string]]::new()
        $seen = New-Object 'System.Collections.Generic.HashSet[string]'
        $stack.Push($a); [void]$seen.Add($a)
        $reached = $false
        while ($stack.Count -and -not $reached) {
            $cur = $stack.Pop()
            foreach ($nxt in $succ[$cur]) {
                if ($cur -eq $a -and $nxt -eq $b) { continue }   # the edge itself
                if ($nxt -eq $b) { $reached = $true; break }
                if ($seen.Add($nxt)) { $stack.Push($nxt) }
            }
        }
        if (-not $reached) { [void]$keep.Add($e) }
    }
    return $keep
}

function Get-Header([string]$Title) {
    @("%% $Title",
      '%% Generated by scripts\dep_graph.ps1 from real proof dependencies.',
      '%% Solid edge: a proof or statement mentions the target.',
      '',
      'graph BT')
}

function Get-Styles {
    @('',
      '  classDef facade stroke-width:3px,stroke:#1d7a55,fill:#e7f4ee,color:#12291f;',
      '  classDef orphan stroke-dasharray:4 3,stroke:#96620f,fill:#fbf1de,color:#2a2113;')
}

# --- renderers ----------------------------------------------------------------
function Render-Family {
    $famEdges = @{}
    foreach ($e in $moduleEdges) {
        $p = $e -split "`t"
        $fa = Get-Family $p[0]; $fb = Get-Family $p[1]
        if ($fa -ne $fb) {
            $k = "$fa`t$fb"
            $famEdges[$k] = 1 + ($famEdges[$k] ?? 0)
        }
    }
    $counts = @{}
    foreach ($m in $allModules) { $f = Get-Family $m; $counts[$f] = 1 + ($counts[$f] ?? 0) }

    $out = [System.Collections.Generic.List[string]]::new()
    $out.AddRange([string[]](Get-Header 'ECRuntime proof architecture, by family'))
    foreach ($f in ($counts.Keys | Sort-Object)) {
        $out.Add("  $(Get-NodeId $f)[`"$f<br/><small>$($counts[$f]) modules</small>`"]")
    }
    $out.Add('')
    foreach ($k in ($famEdges.Keys | Sort-Object { -$famEdges[$_] })) {
        $p = $k -split "`t"
        $out.Add("  $(Get-NodeId $p[0]) -->|$($famEdges[$k])| $(Get-NodeId $p[1])")
    }
    $out.AddRange([string[]](Get-Styles))
    return $out -join "`n"
}

function Render-Modules {
    $medges = if ($NoReduce) { $moduleEdges } else { Get-TransitiveReduction $moduleEdges }
    $declaring = $declModule.Values | Sort-Object -Unique
    $reexport = $allModules | Where-Object { $_ -notin $declaring }

    $byFamily = @{}
    foreach ($m in ($allModules | Sort-Object)) {
        $f = Get-Family $m
        if (-not $byFamily.ContainsKey($f)) { $byFamily[$f] = [System.Collections.Generic.List[string]]::new() }
        $byFamily[$f].Add($m)
    }

    $out = [System.Collections.Generic.List[string]]::new()
    $out.AddRange([string[]](Get-Header 'ECRuntime module dependencies (transitively reduced)'))
    $out.Insert(3, '%% Dashed edge: re-export only -- the module declares nothing itself.')
    foreach ($f in ($byFamily.Keys | Sort-Object)) {
        $out.Add("  subgraph $(Get-SubgraphId $f)[`"$f`"]")
        foreach ($m in $byFamily[$f]) { $out.Add("    $(Get-NodeId $m)[`"$m`"]") }
        $out.Add('  end')
    }
    $out.Add('')
    foreach ($e in ($medges | Sort-Object)) {
        $p = $e -split "`t"
        $out.Add("  $(Get-NodeId $p[0]) --> $(Get-NodeId $p[1])")
    }
    foreach ($m in $reexport) {
        foreach ($d in $moduleImports[$m]) {
            if ($d -in $allModules) { $out.Add("  $(Get-NodeId $m) -.-> $(Get-NodeId $d)") }
        }
    }
    $out.AddRange([string[]](Get-Styles))
    $fac = $Facades | Where-Object { $_ -in $allModules } | Sort-Object
    $orp = $OrphanAllowlist | Where-Object { $_ -in $allModules } | Sort-Object
    if ($fac) { $out.Add("  class $(($fac | ForEach-Object { Get-NodeId $_ }) -join ',') facade;") }
    if ($orp) { $out.Add("  class $(($orp | ForEach-Object { Get-NodeId $_ }) -join ',') orphan;") }
    return $out -join "`n"
}

function Render-Neighbourhood([string]$Target) {
    if ($Target -notin $allModules) { Write-Error "no module named $Target"; exit 2 }
    $ups = @(); $downs = @()
    foreach ($e in $moduleEdges) {
        $p = $e -split "`t"
        if ($p[1] -eq $Target) { $ups += $p[0] }
        if ($p[0] -eq $Target) { $downs += $p[1] }
    }
    $out = [System.Collections.Generic.List[string]]::new()
    $out.AddRange([string[]](Get-Header "${Target}: direct proof dependencies"))
    $out.Add("  $(Get-NodeId $Target)[`"$Target`"]")
    foreach ($m in ($downs | Sort-Object -Unique)) {
        $out.Add("  $(Get-NodeId $m)[`"$m`"]")
        $out.Add("  $(Get-NodeId $Target) --> $(Get-NodeId $m)")
    }
    foreach ($m in ($ups | Sort-Object -Unique)) {
        $out.Add("  $(Get-NodeId $m)[`"$m`"]")
        $out.Add("  $(Get-NodeId $m) --> $(Get-NodeId $Target)")
    }
    $out.AddRange([string[]](Get-Styles))
    $out.Add("  class $(Get-NodeId $Target) facade;")
    return $out -join "`n"
}

function Render-Theorem([string]$Root, [int]$MaxDepth) {
    $full = if ($Root.StartsWith('ECRuntime.')) { $Root } else { "ECRuntime.$Root" }
    if (-not $declModule.ContainsKey($full)) {
        $cands = @($declModule.Keys | Where-Object { $_.EndsWith(".$Root") })
        if ($cands.Count -ne 1) { Write-Error "no declaration $full"; exit 2 }
        $full = $cands[0]
    }
    $succ = @{}
    foreach ($e in $edges) {
        if (-not $succ.ContainsKey($e[0])) { $succ[$e[0]] = [System.Collections.Generic.List[string]]::new() }
        $succ[$e[0]].Add($e[1])
    }
    $level = @{ $full = 0 }
    $order = [System.Collections.Generic.List[string]]::new(); $order.Add($full)
    $frontier = @($full)
    for ($d = 1; $d -le $MaxDepth; $d++) {
        $next = @()
        foreach ($cur in $frontier) {
            foreach ($t in ($succ[$cur] | Sort-Object -Unique)) {
                if (-not $level.ContainsKey($t)) { $level[$t] = $d; $order.Add($t); $next += $t }
            }
        }
        $frontier = $next
    }
    $out = [System.Collections.Generic.List[string]]::new()
    $out.AddRange([string[]](Get-Header "$($full -replace '^ECRuntime\.','') : proof dependencies, depth $MaxDepth"))
    foreach ($n in $order) {
        $short = $n -replace '^ECRuntime\.', ''
        $out.Add("  $(Get-NodeId $n)[`"$short<br/><small>$($declModule[$n])</small>`"]")
    }
    $out.Add('')
    foreach ($a in $order) {
        foreach ($b in ($succ[$a] | Sort-Object -Unique)) {
            if ($level.ContainsKey($b)) { $out.Add("  $(Get-NodeId $a) --> $(Get-NodeId $b)") }
        }
    }
    $out.AddRange([string[]](Get-Styles))
    $out.Add("  class $(Get-NodeId $full) facade;")
    return $out -join "`n"
}

function Render-RedundantImports {
    # An import is NOT redundant merely because nothing in it is mentioned: it may be
    # the only route to a module that is. ExpectedRuntimeCorollaries mentions nothing
    # from LinearRuntime, yet dropping that import breaks the build, because it is how
    # OneMax arrives. So an import is removable only when every module this one
    # actually depends on stays reachable through the imports that remain.
    function Closure([string[]]$roots) {
        $seen = New-Object 'System.Collections.Generic.HashSet[string]'
        $stack = [System.Collections.Generic.Stack[string]]::new()
        foreach ($r in $roots) { $stack.Push($r) }
        while ($stack.Count) {
            $cur = $stack.Pop()
            if ($seen.Add($cur)) { foreach ($d in $moduleImports[$cur]) { $stack.Push($d) } }
        }
        return $seen
    }
    $lines = [System.Collections.Generic.List[string]]::new()
    $total = 0
    foreach ($m in ($allModules | Sort-Object)) {
        $needed = @()
        foreach ($e in $moduleEdges) { $p = $e -split "`t"; if ($p[0] -eq $m) { $needed += $p[1] } }
        $needed = $needed | Sort-Object -Unique
        $removable = @()
        foreach ($cand in $moduleImports[$m]) {
            $rest = @($moduleImports[$m] | Where-Object { $_ -ne $cand })
            $reach = Closure $rest
            if (-not ($needed | Where-Object { -not $reach.Contains($_) })) { $removable += $cand }
        }
        $total += $removable.Count
        if ($removable) {
            $lines.Add("${m}:  (depends on $($needed.Count) module(s))")
            foreach ($d in $removable) { $lines.Add("    import ECRuntime.$d") }
        }
    }
    $head = @(
        "$total import(s) are individually removable: every module the importer actually",
        'depends on stays reachable without them. Candidates, not a verdict -- an import',
        'can also carry notation or a scoped instance that no proof term mentions.',
        'Elaborate before deleting.',
        ''
    )
    return (($head + $lines) -join "`n")
}

# --- dispatch -----------------------------------------------------------------
$text =
    if     ($RedundantImports) { Render-RedundantImports }
    elseif ($Theorem)          { Render-Theorem $Theorem $Depth }
    elseif ($Module)           { Render-Neighbourhood $Module }
    elseif ($Level -eq 'family') { Render-Family }
    else                       { Render-Modules }

if ($Output) {
    $dir = Split-Path -Parent $Output
    if ($dir -and -not (Test-Path $dir)) { New-Item -ItemType Directory -Path $dir -Force | Out-Null }
    [IO.File]::WriteAllText($Output, $text + "`n", [Text.UTF8Encoding]::new($false))
    Write-Output "wrote $Output"
} else {
    Write-Output $text
}
