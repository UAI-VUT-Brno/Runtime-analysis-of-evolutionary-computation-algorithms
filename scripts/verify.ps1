<#
.SYNOPSIS
  ECRuntime verification runner. Every gate must pass; warnings count as failures.

.DESCRIPTION
  Replaces the per-stage runners (run_stage79_fix1.sh and predecessors). The stage is
  a parameter, not part of the filename, so promoting a stage no longer means editing
  the runner, the exporter and README in lockstep.

  Results are written inside the repository under the ignored .verify\ directory.
  Nothing is written outside the repository root.

  One exception, deliberately: the `graphs` gate regenerates docs\current\graphs\*.mmd, which
  are generated artifacts rather than sources. It reports when they change, so a run
  never alters a tracked file silently.

.PARAMETER Stage
  Stage label, e.g. 80. Used only to name the results directory.

.PARAMETER Focus
  Module to build first, e.g. ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain.

.PARAMETER Candidate
  Permit `sorry`. A candidate run is never promotable, however green.

.PARAMETER Quick
  Skip the dependency cache fetch and the export. Inner development loop only.

.EXAMPLE
  pwsh -File scripts\verify.ps1 -Stage 80 -Focus ECRuntime.SomeNewModule
#>
[CmdletBinding()]
param(
    [Parameter(Mandatory)][ValidatePattern('^[A-Za-z0-9._-]+$')][string]$Stage,
    [string]$Focus,
    [switch]$Candidate,
    [switch]$Quick
)

$ErrorActionPreference = 'Continue'
$repo = Split-Path -Parent $PSScriptRoot

$outDir = Join-Path $repo ".verify\stage-$Stage"
if (Test-Path -LiteralPath $outDir) { Remove-Item -LiteralPath $outDir -Recurse -Force }
New-Item -ItemType Directory -Path $outDir -Force | Out-Null

$gates = [ordered]@{}

function Invoke-Gate {
    param([string]$Name, [scriptblock]$Command)
    Write-Output "===== $Name ====="
    $log = Join-Path $outDir "$Name.log"
    & $Command 2>&1 | Tee-Object -FilePath $log
    $rc = $LASTEXITCODE
    if ($null -eq $rc) { $rc = 0 }
    $gates[$Name] = $rc
    if ($rc -ne 0) { Write-Output "  -> $Name FAILED (rc=$rc)" }
}

# --- environment --------------------------------------------------------------
@(
    "stage=$Stage"
    "focus=$(if ($Focus) { $Focus } else { '<none>' })"
    "candidate=$([int]$Candidate.IsPresent)"
    "timestamp_utc=$([DateTime]::UtcNow.ToString('yyyy-MM-ddTHH:mm:ssZ'))"
    "repo_root=$repo"
    "lean=$((& lean --version) -join ' ')"
    "lake=$((& lake --version) -join ' ')"
    "toolchain=$(Get-Content (Join-Path $repo 'lean-toolchain') -ErrorAction SilentlyContinue)"
) | Set-Content -Path (Join-Path $outDir 'environment.txt') -Encoding utf8

# --- gate 1: root aggregator --------------------------------------------------
$gates['root_aggregator'] = if (Test-Path -LiteralPath (Join-Path $repo 'ECRuntime.lean')) { 0 } else {
    Write-Output 'error: ECRuntime.lean is missing'; 1
}

# --- gate 2: source hygiene ---------------------------------------------------
# Runs inside Lean, so the checks read the real environment instead of guessing at
# source text with regexes.
$auditArgs = if ($Candidate) { 'candidate' } else { 'strict' }
Invoke-Gate 'hygiene' { & lake env lean --run (Join-Path $repo 'scripts\audit.lean') $auditArgs }

# --- gates 3-6: builds --------------------------------------------------------
if ($Quick) { $gates['cache_get'] = 0 }
else { Invoke-Gate 'cache_get' { & lake exe cache get } }

if ($Focus) { Invoke-Gate 'focused_build' { & lake build $Focus } }
else { $gates['focused_build'] = 0 }

Invoke-Gate 'full_build' { & lake build ECRuntime }
Invoke-Gate 'test_build' { & lake build ECRuntimeTest }

# --- gate 7: zero diagnostics -------------------------------------------------
# A clean exit code is not enough: `lake build` exits 0 on warnings, and
# DEVELOPMENT.md section 2 counts warnings as promotion failures.
$dirty = 0
foreach ($name in 'focused_build', 'full_build', 'test_build') {
    $log = Join-Path $outDir "$name.log"
    if ((Test-Path -LiteralPath $log) -and
        (Select-String -LiteralPath $log -Pattern '(^|\s)(error|warning):' -Quiet)) {
        $dirty = 1
    }
}
$gates['diagnostics_clean'] = $dirty

# --- gate 8: dependency graphs ------------------------------------------------
# The one gate that writes a tracked file. docs\current\graphs\*.mmd are generated artifacts --
# regenerated, never hand-edited -- but for a long time nothing regenerated them,
# so they drifted. That is the same staleness that left the old Python tooling dead for
# months. Runs before the export so the archive carries current graphs.
$graphFiles = @('architecture.mmd', 'modules.mmd')
if ($Quick) { $gates['graphs'] = 0 }
else {
    $graphDir = Join-Path $repo 'docs/current/graphs'
    $before = @{}
    foreach ($f in $graphFiles) {
        $gp = Join-Path $graphDir $f
        if (Test-Path -LiteralPath $gp) {
            $before[$f] = (Get-FileHash -LiteralPath $gp -Algorithm SHA256).Hash
        }
    }
    Invoke-Gate 'graphs' {
        & lake env lean --run (Join-Path $repo 'scripts\audit.lean') `
            graph --all --outdir $graphDir
    }
    $changed = @()
    foreach ($f in $graphFiles) {
        $gp = Join-Path $graphDir $f
        if (Test-Path -LiteralPath $gp) {
            if ($before[$f] -ne (Get-FileHash -LiteralPath $gp -Algorithm SHA256).Hash) {
                $changed += $f
            }
        }
    }
    if ($changed.Count) {
        Write-Output "  -> graphs regenerated and CHANGED: $($changed -join ', ')"
        Write-Output "     the proof-dependency network moved; commit the regenerated files"
    } else {
        Write-Output "  -> graphs unchanged"
    }
}

# --- gate 9: export -----------------------------------------------------------
if ($Quick) { $gates['export'] = 0 }
else {
    Invoke-Gate 'export' {
        & pwsh -NoProfile -File (Join-Path $repo 'scripts\export_repository.ps1') `
            -Version "stage-$Stage" `
            -Output (Join-Path $outDir "ECRuntime_stage-$Stage`_repository.zip")
    }
}

# --- verdict ------------------------------------------------------------------
$overall = if (($gates.Values | Where-Object { $_ -ne 0 }).Count) { 1 } else { 0 }
$gates['overall'] = $overall

$promotable =
    if ($overall -ne 0) { 'no (a gate failed)' }
    elseif ($Candidate) { 'no (candidate run: sorry permitted)' }
    else { 'yes' }

$statusPath = Join-Path $outDir 'status.txt'
($gates.GetEnumerator() | ForEach-Object { "$($_.Key)=$($_.Value)" }) |
    Set-Content -Path $statusPath -Encoding utf8

# --- review summary -----------------------------------------------------------
$review = [System.Collections.Generic.List[string]]::new()
$review.Add("ECRuntime verification -- stage $Stage")
$review.Add('')
$review.Add('===== environment =====')
$review.AddRange([string[]](Get-Content (Join-Path $outDir 'environment.txt')))
$review.Add('')
$review.Add('===== gates =====')
$review.AddRange([string[]](Get-Content $statusPath))
$review.Add('')
$review.Add("promotable: $promotable")
$review.Add('')
$review.Add('===== diagnostics =====')
$found = $false
foreach ($log in Get-ChildItem -LiteralPath $outDir -Filter *.log) {
    $hits = Select-String -LiteralPath $log.FullName -Pattern '(^|\s)(error|warning):'
    if ($hits) {
        $found = $true
        $review.Add("--- $($log.Name) ---")
        $hits | ForEach-Object { $review.Add("$($_.LineNumber): $($_.Line.Trim())") }
    }
}
if (-not $found) { $review.Add('No error:/warning: lines found.') }
$review | Set-Content -Path (Join-Path $outDir 'review.txt') -Encoding utf8

Write-Output ''
Get-Content $statusPath
Write-Output ''
Write-Output "promotable:  $promotable"
Write-Output "review:      $(Join-Path $outDir 'review.txt')"
exit $overall
