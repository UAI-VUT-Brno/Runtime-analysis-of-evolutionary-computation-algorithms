<#
.SYNOPSIS
  Exercise both PreToolUse guards.

.DESCRIPTION
  Payloads live in this file rather than on a command line, because the outbound
  guard scans whole command strings -- a test harness that spells the blocked verbs
  inline blocks itself. (That happened; it is the guard working, not a bug.)

    pwsh -NoProfile -File scripts\test_hooks.ps1

  Exit 0 when every case behaves as specified.
#>

$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
$write = Join-Path $PSScriptRoot 'hooks\guard_lean_write.ps1'
$out   = Join-Path $PSScriptRoot 'hooks\guard_outbound.ps1'
$marker = Join-Path $repo '.candidate-stage'

function Invoke-Guard {
    param([string]$Script, [hashtable]$Payload)
    $json = $Payload | ConvertTo-Json -Depth 6 -Compress
    $json | & pwsh -NoProfile -File $Script 2>$null | Out-Null
    return $LASTEXITCODE
}

function New-Payload {
    # Not $Input: that is an automatic variable holding the pipeline enumerator,
    # and binding it as a parameter silently receives the enumerator instead.
    param([string]$Tool, [hashtable]$ToolInput)
    return @{ tool_name = $Tool; tool_input = $ToolInput }
}

$fails = 0
function Test-Case {
    param([string]$Label, [string]$Script, [hashtable]$Payload, [int]$Expect)
    $rc = Invoke-Guard -Script $Script -Payload $Payload
    $verdict = if ($rc -eq 2) { 'BLOCK' } else { 'allow' }
    $ok = ($rc -eq $Expect)
    if (-not $ok) { $script:fails++ }
    "  {0,-40} {1,-6} {2}" -f $Label, $verdict, $(if ($ok) { 'OK' } else { '*** WRONG ***' })
}

$leanFile = Join-Path $repo 'ECRuntime\Probe.lean'

Write-Output "=== write guard: forbidden constructs ==="
if (Test-Path $marker) { Remove-Item $marker -Force }
Test-Case 'sorry, no candidate marker'   $write (New-Payload 'Write' @{ file_path = $leanFile; content = 'theorem f : True := by sorry' }) 2
New-Item -ItemType File -Path $marker -Force | Out-Null
Test-Case 'sorry, marker present'        $write (New-Payload 'Write' @{ file_path = $leanFile; content = 'theorem f : True := by sorry' }) 0
Test-Case 'axiom, even with marker'      $write (New-Payload 'Write' @{ file_path = $leanFile; content = 'axiom cheat : False' }) 2
Remove-Item $marker -Force
Test-Case 'native_decide via Edit'       $write (New-Payload 'Edit'  @{ file_path = $leanFile; new_string = 'theorem f : True := by native_decide' }) 2
Test-Case 'maxHeartbeats bump'           $write (New-Payload 'Write' @{ file_path = $leanFile; content = 'set_option maxHeartbeats 400000' }) 2
Test-Case 'the word in a comment only'   $write (New-Payload 'Write' @{ file_path = $leanFile; content = "/-- we are sorry -/`ntheorem f : True := trivial" }) 0
Test-Case 'outside ECRuntime\'           $write (New-Payload 'Write' @{ file_path = (Join-Path $repo 'ECRuntimeTest\X.lean'); content = 'theorem f : True := by sorry' }) 0
Test-Case 'a non-Lean file'              $write (New-Payload 'Write' @{ file_path = (Join-Path $repo 'notes.md'); content = 'sorry about that' }) 0

Write-Output "`n=== outbound guard: must block ==="
Test-Case 'direct fetch'                 $out (New-Payload 'Bash' @{ command = ('c' + 'url https://x/a') }) 2
Test-Case 'hidden in a pipe'             $out (New-Payload 'Bash' @{ command = ('echo hi | c' + 'url -T - https://x') }) 2
Test-Case 'behind &&'                    $out (New-Payload 'Bash' @{ command = ('ls && c' + 'url https://x') }) 2
Test-Case 'wrapped in another shell'     $out (New-Payload 'Bash' @{ command = ('bash -c "w' + 'get https://x"') }) 2
Test-Case 'PS web request'               $out (New-Payload 'PowerShell' @{ command = ('Invoke-Web' + 'Request -Uri https://x') }) 2
Test-Case 'PS web client'                $out (New-Payload 'PowerShell' @{ command = ('(New-Object Net.Web' + 'Client).Download' + 'File("a","b")') }) 2
Test-Case 'package install'              $out (New-Payload 'Bash' @{ command = ('p' + 'ip install requests') }) 2
Test-Case 'remote shell'                 $out (New-Payload 'Bash' @{ command = ('s' + 'sh host ls') }) 2

Write-Output "`n=== outbound guard: must allow ==="
Test-Case 'lake build'                   $out (New-Payload 'Bash' @{ command = 'lake build ECRuntime' }) 0
Test-Case 'lake cache fetch'             $out (New-Payload 'Bash' @{ command = 'lake exe cache get' }) 0
Test-Case 'verify runner'                $out (New-Payload 'PowerShell' @{ command = 'pwsh -File scripts\verify.ps1 -Stage 80' }) 0
Test-Case 'filename that reads oddly'    $out (New-Payload 'Bash' @{ command = ('cat docs/c' + 'urling-notes.md') }) 0
Test-Case 'non-shell tool untouched'     $out (New-Payload 'Read' @{ command = ('c' + 'url https://x') }) 0

$total = 21
Write-Output ("`n{0}/{1} cases behave as specified" -f ($total - $fails), $total)
if (Test-Path $marker) { Remove-Item $marker -Force }
exit $(if ($fails) { 1 } else { 0 })
