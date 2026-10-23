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

.EXAMPLE
  pwsh -File scripts\export_repository.ps1 -Version stage-80
#>
[CmdletBinding()]
param(
    [string]$Output,
    [string]$Version = 'ECRuntime'
)

$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.IO.Compression.FileSystem

$repo = Split-Path -Parent $PSScriptRoot

$RootFiles = @(
    '.gitignore', '.gitattributes', 'README.md',
    'DEVELOPMENT.md', 'HISTORY.md', 'CLAUDE.md', 'SOUL.md',
    'ECRuntime.lean', 'ECRuntimeTest.lean', 'run_verification.sh', 'lakefile.toml',
    'lake-manifest.json', 'lean-toolchain'
)
$Optional = @('CLAUDE.md', 'SOUL.md', 'lake-manifest.json')
# Export all maintained directories. The candidate-stage marker is intentionally
# absent after the Stage 166 promotion; future active candidates are exported
# only as regular files in candidates/, with their approved signature record.
$SourceDirs = @('ECRuntime', 'ECRuntimeTest', 'candidates',
                'docs', 'scripts', '.claude')

function Get-RelativePath {
    param([string]$Full)
    return $Full.Substring($repo.Length).TrimStart('\', '/').Replace('\', '/')
}

# --- collect -----------------------------------------------------------------
$files = [System.Collections.Generic.List[string]]::new()

foreach ($rel in $RootFiles) {
    $path = Join-Path $repo $rel
    if (Test-Path -LiteralPath $path -PathType Leaf) {
        $files.Add((Resolve-Path -LiteralPath $path).Path)
    } elseif ($Optional -notcontains $rel) {
        Write-Error "required maintained file is missing: $rel"
        exit 3
    }
}

# Only the stable, maintained runner is exported. Historical per-round
# wrapper scripts were retired after the verified Round56 consolidation.

foreach ($dir in $SourceDirs) {
    $path = Join-Path $repo $dir
    if (-not (Test-Path -LiteralPath $path -PathType Container)) {
        Write-Error "required maintained source directory is missing: $dir"
        exit 3
    }
    Get-ChildItem -LiteralPath $path -Recurse -File |
        Where-Object {
            $_.Name -notmatch '(?i)\.(pyc|log)$' -and
            $_.Name -ne 'settings.local.json' -and
            $_.FullName -notmatch '[\\/]__pycache__[\\/]'
        } | Sort-Object FullName |
        ForEach-Object { $files.Add($_.FullName) }
}

$files = $files | Sort-Object { Get-RelativePath $_ } -Unique

# --- manifest ----------------------------------------------------------------
$rows = [System.Collections.Generic.List[string]]::new()
$rows.Add("# $Version source manifest")
$rows.Add("# files=$($files.Count)")
foreach ($f in $files) {
    $hash = (Get-FileHash -LiteralPath $f -Algorithm SHA256).Hash.ToLowerInvariant()
    $rows.Add("$hash  $(Get-RelativePath $f)")
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
            $zip, $f, "ECRuntime/$(Get-RelativePath $f)", 'Optimal') | Out-Null
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
