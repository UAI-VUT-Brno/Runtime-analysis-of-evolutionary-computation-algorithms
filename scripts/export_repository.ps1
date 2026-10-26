<#
.SYNOPSIS
  Export the ECRuntime checkout as a clean source ZIP plus manifest.

.DESCRIPTION
  Source-only and reproducible (DEVELOPMENT.md section 9): a repository ZIP, a
  SHA-256 sidecar, and a deterministic per-file manifest. Files are whitelisted, so a
  stray artifact in the working tree is a hygiene failure rather than something that
  silently ships.

  Stage-agnostic: the stage is a caller's concern, not part of this filename.

  Uses System.IO.Compression directly rather than Compress-Archive, because entry
  names need an explicit `ECRuntime/` prefix and a generated manifest has to be
  written into the archive without ever existing on disk.

.PARAMETER Output
  Destination ZIP path. Defaults to .verify\<Version>_repository.zip.

.PARAMETER Version
  Label recorded in the manifest header.

.PARAMETER Profile
  `private` (default) or `public`. Both export the same maintained files, including the
  Claude Code setup (CLAUDE.md, SOUL.md, .claude/settings.json, .claude/agents,
  .claude/skills, the guard hooks and their test). They differ only in where the CI
  workflow lands: `public` publishes scripts/public/ci.yml as .github/workflows/ci.yml.
  .claude/settings.local.json holds one machine's permission grants and is never exported.

.EXAMPLE
  pwsh -File scripts\export_repository.ps1 -Version stage-80

.EXAMPLE
  pwsh -File scripts\export_repository.ps1 -Profile public -Version public-2026-10-26
#>
[CmdletBinding()]
param(
    [string]$Output,
    [string]$Version = 'ECRuntime',
    [ValidateSet('private', 'public')][string]$Profile = 'private'
)

$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.IO.Compression.FileSystem

$repo = Split-Path -Parent $PSScriptRoot

$RootFiles = @(
    '.gitignore', '.gitattributes', 'README.md', 'DEVELOPMENT.md', 'HISTORY.md',
    'LICENSE', 'CONTRIBUTING.md', 'CONTRIBUTORS.md', 'CODE_OF_CONDUCT.md', 'CITATION.cff',
    'ECRuntime.lean', 'ECRuntimeTest.lean', 'lakefile.toml', 'lake-manifest.json',
    'lean-toolchain'
)
# The fixed documents of docs/. The per-paper and per-line files are matched by $Globs.
$DocFiles = @(
    'docs/README.md',
    'docs/current/README.md',
    'docs/current/facades.md',
    'docs/history/README.md',
    'docs/history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md',
    'docs/history/archive/PROJECT_STATE.tex',
    'docs/roadmap/README.md',
    'docs/roadmap/TEMPLATE-paper.md',
    'docs/roadmap/frontier.toml',
    'docs/roadmap/papers/README.md'
)
$ScriptFiles = @(
    'scripts/verify.ps1',
    'scripts/export_repository.ps1',
    'scripts/facade_index.ps1',
    'scripts/docs_index.ps1',
    'scripts/audit.lean'
)
$GitHubFiles = @(
    '.github/CODEOWNERS',
    '.github/PULL_REQUEST_TEMPLATE.md',
    '.github/audit-baseline.txt',
    '.github/ISSUE_TEMPLATE/config.yml',
    '.github/ISSUE_TEMPLATE/statement-proposal.md',
    '.github/ISSUE_TEMPLATE/mismatch-or-error.md',
    # The CI workflow. The private repository keeps it in scripts/public/ so that GitHub
    # does not run it there; the public repository has it in .github/workflows/.
    'scripts/public/ci.yml',
    '.github/workflows/ci.yml'
)
# Source path -> path in the public archive.
$PublicRename = @{ 'scripts/public/ci.yml' = '.github/workflows/ci.yml' }
# The Claude Code setup: the agents' working rules, the permission and hook configuration,
# and the guards the hooks run. Published in both profiles so that a clone works the same.
$AgentFiles = @(
    'CLAUDE.md', 'SOUL.md',
    '.claude/settings.json',
    'scripts/test_hooks.ps1',
    'scripts/hooks/guard_lean_write.ps1',
    'scripts/hooks/guard_outbound.ps1'
)
$Listed = $RootFiles + $DocFiles + $ScriptFiles + $GitHubFiles + $AgentFiles
# Present in a working tree but never required; exported when found.
$Optional = @('lake-manifest.json',
              'scripts/public/ci.yml', '.github/workflows/ci.yml')
$LeanDirs = @('ECRuntime', 'ECRuntimeTest')
# .claude/settings.local.json is deliberately not matched: it is one machine's grants.
$Globs    = @('docs/current/graphs/*.mmd', 'docs/history/archive/graphs/*.mmd', 'docs/current/papers/*.md',
              'docs/history/*.md', 'docs/roadmap/papers/*.md',
              '.claude/agents/*.md', '.claude/skills/*/SKILL.md')

function Get-RelativePath {
    param([string]$Full)
    return $Full.Substring($repo.Length).TrimStart('\', '/').Replace('\', '/')
}

# The path a file takes inside the archive and the manifest.
function Get-ArchivePath {
    param([string]$Full)
    $rel = Get-RelativePath $Full
    if ($Profile -eq 'public' -and $PublicRename.ContainsKey($rel)) { return $PublicRename[$rel] }
    return $rel
}

# --- collect -----------------------------------------------------------------
$files = [System.Collections.Generic.List[string]]::new()

foreach ($rel in $Listed) {
    $path = Join-Path $repo $rel
    if (Test-Path -LiteralPath $path -PathType Leaf) {
        $files.Add((Resolve-Path -LiteralPath $path).Path)
    } elseif ($Optional -notcontains $rel) {
        Write-Error "required maintained file is missing: $rel"
        exit 3
    }
}

foreach ($dir in $LeanDirs) {
    $found = Get-ChildItem -LiteralPath (Join-Path $repo $dir) -Filter *.lean -File |
             Sort-Object Name
    if (-not $found) { Write-Error "no maintained $dir/*.lean files found"; exit 3 }
    $found | ForEach-Object { $files.Add($_.FullName) }
}

foreach ($glob in $Globs) {
    Get-ChildItem -Path (Join-Path $repo $glob) -File -ErrorAction SilentlyContinue |
        Sort-Object FullName | ForEach-Object { $files.Add($_.FullName) }
}

$files = $files | Sort-Object { Get-ArchivePath $_ } -Unique

# --- manifest ----------------------------------------------------------------
$rows = [System.Collections.Generic.List[string]]::new()
$rows.Add("# $Version source manifest ($Profile profile)")
$rows.Add("# files=$($files.Count)")
foreach ($f in $files) {
    $hash = (Get-FileHash -LiteralPath $f -Algorithm SHA256).Hash.ToLowerInvariant()
    $rows.Add("$hash  $(Get-ArchivePath $f)")
}
$manifestText = ($rows -join "`n") + "`n"

# --- archive -----------------------------------------------------------------
if (-not $Output) {
    $Output = Join-Path $repo ".verify\${Version}_repository.zip"
}
$outDir = Split-Path -Parent $Output
if ($outDir -and -not (Test-Path -LiteralPath $outDir)) {
    New-Item -ItemType Directory -Path $outDir -Force | Out-Null
}
$Output = [System.IO.Path]::GetFullPath($Output)

# Build atomically, then write the sidecars describing it, so a failed run cannot
# leave a manifest for an archive that does not exist.
$tmp = "$Output.tmp"
if (Test-Path -LiteralPath $tmp) { Remove-Item -LiteralPath $tmp -Force }

$zip = [System.IO.Compression.ZipFile]::Open($tmp, 'Create')
try {
    foreach ($f in $files) {
        [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile(
            $zip, $f, "ECRuntime/$(Get-ArchivePath $f)", 'Optimal') | Out-Null
    }
    $entry = $zip.CreateEntry('ECRuntime/EXPORT_MANIFEST.txt', 'Optimal')
    $writer = [System.IO.StreamWriter]::new($entry.Open(), [System.Text.UTF8Encoding]::new($false))
    $writer.Write($manifestText)
    $writer.Dispose()
} finally {
    $zip.Dispose()
}
Move-Item -LiteralPath $tmp -Destination $Output -Force

$manifestPath = [System.IO.Path]::ChangeExtension($Output, $null).TrimEnd('.') + '.manifest.txt'
[System.IO.File]::WriteAllText($manifestPath, $manifestText, [System.Text.UTF8Encoding]::new($false))

$digest = (Get-FileHash -LiteralPath $Output -Algorithm SHA256).Hash.ToLowerInvariant()
$sidecar = "$Output.sha256"
[System.IO.File]::WriteAllText($sidecar, "$digest  $(Split-Path -Leaf $Output)`n",
                               [System.Text.UTF8Encoding]::new($false))

Write-Output "Repository source archive: $Output"
Write-Output "SHA-256 sidecar:           $sidecar"
Write-Output "Source manifest:           $manifestPath"
Write-Output "Included maintained files: $($files.Count)"
exit 0
