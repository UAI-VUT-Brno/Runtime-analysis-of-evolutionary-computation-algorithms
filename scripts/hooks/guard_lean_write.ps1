<#
.SYNOPSIS
  PreToolUse guard: keep proof-holes out of promoted Lean source.

.DESCRIPTION
  Reads the Claude Code hook payload on stdin. Blocks an Edit/Write that would put
  `sorry`, a new `axiom`, `native_decide`, `unsafe`, or a `maxHeartbeats` bump into
  ECRuntime\*.lean.

  `sorry` is legitimate while a stage is being built: a statement skeleton is written
  first and discharged afterwards. Create the marker file `.candidate-stage` at the
  repository root to allow it, and delete the marker before promoting. The other
  constructs are never permitted -- no stage has ever needed one.

  Exit 0 to allow, exit 2 with a reason on stderr to block.
#>

$ErrorActionPreference = 'Stop'

$repo   = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$marker = Join-Path $repo '.candidate-stage'

# Never break the session on a malformed payload.
try {
    $raw = [Console]::In.ReadToEnd()
    if ([string]::IsNullOrWhiteSpace($raw)) { exit 0 }
    $payload = $raw | ConvertFrom-Json
} catch { exit 0 }

$tool = [string]$payload.tool_name
$args = $payload.tool_input
if ($null -eq $args) { exit 0 }

$path = [string]($args.file_path)
if ([string]::IsNullOrWhiteSpace($path)) { $path = [string]($args.notebook_path) }
if ([string]::IsNullOrWhiteSpace($path)) { exit 0 }

# Only guard Lean sources inside this repository's ECRuntime directory.
# The trailing separator matters: without it the prefix test also matches sibling
# directories whose names merely start the same way, and ECRuntimeTest\ is exactly
# such a sibling.
try { $full = [System.IO.Path]::GetFullPath($path) } catch { exit 0 }
$guarded = [System.IO.Path]::GetFullPath((Join-Path $repo 'ECRuntime')) +
           [System.IO.Path]::DirectorySeparatorChar
if (-not $full.StartsWith($guarded, [StringComparison]::OrdinalIgnoreCase)) { exit 0 }
if (-not $full.EndsWith('.lean', [StringComparison]::OrdinalIgnoreCase)) { exit 0 }

$content = switch ($tool) {
    'Write'        { [string]$args.content }
    'Edit'         { [string]$args.new_string }
    'NotebookEdit' { [string]$args.new_source }
    default        { '' }
}
if ([string]::IsNullOrWhiteSpace($content)) { exit 0 }

# Comments are prose; the word "sorry" in a docstring is not a proof hole.
$body = [regex]::Replace($content, '(?s)/-.*?-/', '')
$body = [regex]::Replace($body, '(?m)--.*$', '')

$rel = $full.Substring($repo.Length).TrimStart('\', '/')

$always = @(
    @{ Label = 'axiom'
       Pattern = '(?m)^\s*axiom\s'
       Why = 'introduces a new axiom; the facade theorems depend on exactly [propext, Classical.choice, Quot.sound] and ECRuntimeTest\AxiomAudit.lean pins that' },
    @{ Label = 'native_decide'
       Pattern = '\bnative_decide\b'
       Why = 'trusts evaluation outside the kernel' },
    @{ Label = 'unsafe'
       Pattern = '(?m)^\s*unsafe\s'
       Why = 'bypasses the type checker' },
    @{ Label = 'maxHeartbeats'
       Pattern = 'set_option\s+maxHeartbeats'
       Why = 'the repository contains zero set_option directives by design; see DEVELOPMENT.md section 5' }
)

foreach ($rule in $always) {
    if ($body -match $rule.Pattern) {
        [Console]::Error.WriteLine(@"
Blocked: this edit puts ``$($rule.Label)`` into $rel, which $($rule.Why).
There is no candidate mode for this construct. If the proof will not close, prove a
weaker theorem under a new name or report the obstacle -- do not reshape the statement
until it passes.
"@)
        exit 2
    }
}

if ($body -match '\bsorry\b' -and -not (Test-Path -LiteralPath $marker)) {
    [Console]::Error.WriteLine(@"
Blocked: this edit puts ``sorry`` into $rel while no stage is marked as a candidate.
If you are building a statement skeleton, create the marker first:
    New-Item -ItemType File .candidate-stage
and delete it before promoting. A run with the marker present is never promotable
(scripts\verify.ps1 -Candidate).
"@)
    exit 2
}

exit 0
