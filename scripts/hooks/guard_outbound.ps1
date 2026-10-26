<#
.SYNOPSIS
  PreToolUse guard: nothing leaves this machine, and nothing is fetched onto it,
  unless the user asked for it in that session.

.DESCRIPTION
  The permission `deny` list in .claude\settings.json already blocks the obvious
  invocations, but it matches on a command *prefix*: `curl ...` is caught while
  `echo x | curl ...`, `bash -c "curl ..."` and `cmd && curl ...` are not. This hook
  scans the whole command string instead, for both the Bash and PowerShell tools.

  Blocks: uploading, downloading, publishing, pushing, sending, remote shells.
  Allows: `lake` and `elan`, which fetch the pinned Mathlib build cache and toolchain --
  the only sanctioned network operations.

  Exit 0 to allow, exit 2 with a reason on stderr to block.
#>

$ErrorActionPreference = 'Stop'

try {
    $raw = [Console]::In.ReadToEnd()
    if ([string]::IsNullOrWhiteSpace($raw)) { exit 0 }
    $payload = $raw | ConvertFrom-Json
} catch { exit 0 }

$tool = [string]$payload.tool_name
if ($tool -ne 'Bash' -and $tool -ne 'PowerShell') { exit 0 }

$command = [string]($payload.tool_input.command)
if ([string]::IsNullOrWhiteSpace($command)) { exit 0 }

# Commands permitted even though they may touch the network.
foreach ($ok in @('^\s*lake\b', '^\s*elan\b')) {
    if ($command -match $ok) { exit 0 }
}

$rules = @(
    @{ Label = 'curl / wget'; Pattern = '\b(curl|wget)\b'
       Why = 'transfers data to or from the network' },
    @{ Label = 'PowerShell web request'
       Pattern = '\b(invoke-webrequest|invoke-restmethod|iwr|irm|start-bitstransfer|bitsadmin)\b'
       Why = 'transfers data to or from the network' },
    @{ Label = '.NET web client'
       Pattern = '\b(webclient|downloadfile|downloadstring|uploadfile|uploadstring)\b'
       Why = 'transfers data to or from the network' },
    @{ Label = 'git push';   Pattern = '\bgit\s+push\b'
       Why = 'publishes commits to a remote' },
    @{ Label = 'git remote'; Pattern = '\bgit\s+remote\s+(add|set-url)\b'
       Why = 'wires this repository to a remote' },
    @{ Label = 'git fetch/pull/clone'; Pattern = '\bgit\s+(fetch|pull|clone)\b'
       Why = 'downloads from a remote' },
    @{ Label = 'gh';      Pattern = '\bgh\b';      Why = 'talks to a hosted forge' },
    @{ Label = 'gitea';   Pattern = '\bgitea\b';   Why = 'talks to a remote server' },
    @{ Label = 'jenkins'; Pattern = '\bjenkins\b'; Why = 'talks to a remote server' },
    @{ Label = 'ssh / scp / rsync / sftp'; Pattern = '\b(ssh|scp|rsync|sftp)\b'
       Why = 'opens a remote connection' },
    @{ Label = 'netcat / telnet'; Pattern = '\b(nc|ncat|netcat|telnet)\b'
       Why = 'opens a raw network connection' },
    @{ Label = 'package install'
       Pattern = '\b(pip|pip3|npm|npx|pnpm|yarn|cargo|gem|choco|winget|scoop)\b'
       Why = 'downloads and installs packages' },
    @{ Label = 'script network call'
       Pattern = '\b(urllib|urlopen|requests\.(get|post|put)|httpx|aiohttp|socket)\b'
       Why = 'opens a network connection from a script' },
    @{ Label = 'mail / ftp'; Pattern = '\b(sendmail|mail|mutt|ftp|tftp)\b'
       Why = 'sends data off this machine' }
)

foreach ($rule in $rules) {
    if ($command -match $rule.Pattern) {
        $shown = $command.Trim()
        if ($shown.Length -gt 300) { $shown = $shown.Substring(0, 300) }
        [Console]::Error.WriteLine(@"
Blocked: this command uses ``$($rule.Label)``, which $($rule.Why).

  $shown

Nothing is published, sent, pushed or downloaded from this repository unless the user
asks for it directly. If the user has just asked for this specific action, say so and
let them run it themselves, or have them add it to `permissions.allow` in
.claude\settings.local.json.
Do not work around this by renaming, encoding, or splitting the command.
"@)
        exit 2
    }
}

exit 0
