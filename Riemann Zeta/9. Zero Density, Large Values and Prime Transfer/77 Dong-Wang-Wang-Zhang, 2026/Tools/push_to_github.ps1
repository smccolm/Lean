[CmdletBinding()]
param(
    [Parameter(Position = 0)]
    [string]$CommitMessage,
    [switch]$NoPause,
    [switch]$RebaseBeforePush
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$syncExit = 1
$locationPushed = $false

function Invoke-CheckedGit {
    param([Parameter(Mandatory = $true)][string[]]$GitArguments)
    & git @GitArguments
    if ($LASTEXITCODE -ne 0) {
        throw "git $($GitArguments -join ' ') failed (exit $LASTEXITCODE)."
    }
}

try {
    Push-Location -LiteralPath (Split-Path -Parent $PSScriptRoot)
    $locationPushed = $true
    $repositoryRoot = (Invoke-CheckedGit -GitArguments @('rev-parse', '--show-toplevel')).Trim()
    if ([string]::IsNullOrWhiteSpace($repositoryRoot)) {
        throw 'Git did not return a repository root.'
    }
    Set-Location -LiteralPath $repositoryRoot
    $branch = Invoke-CheckedGit -GitArguments @('symbolic-ref', '--quiet', '--short', 'HEAD')
    if ($branch -cne 'main') {
        throw "Expected branch main; found '$branch'. No changes have been staged."
    }

    Write-Host "Repository: $repositoryRoot"
    Write-Host 'This owner-only action stages ALL repository changes, commits, and pushes origin/main.'
    if (-not $PSBoundParameters.ContainsKey('CommitMessage')) {
        $CommitMessage = Read-Host 'Commit message (required; no default)'
    }
    if ([string]::IsNullOrWhiteSpace($CommitMessage)) {
        throw 'Commit message cannot be empty or whitespace. No changes have been staged.'
    }

    Invoke-CheckedGit -GitArguments @('add', '-A')
    & git diff --cached --quiet
    $diffExit = $LASTEXITCODE
    if ($diffExit -eq 1) {
        Invoke-CheckedGit -GitArguments @('commit', '-m', $CommitMessage)
    } elseif ($diffExit -eq 0) {
        Write-Host 'No new staged changes to commit; checking the push anyway.'
    } else {
        throw "git diff --cached --quiet failed (exit $diffExit)."
    }

    if ($RebaseBeforePush) {
        Write-Host 'Updating local main from origin/main with the owner-selected rebase workflow.'
        Invoke-CheckedGit -GitArguments @('pull', '--rebase', 'origin', 'main')
    }
    Invoke-CheckedGit -GitArguments @('push', 'origin', 'main')
    Write-Host 'Git synchronization completed successfully.'
    $syncExit = 0
} catch {
    [Console]::Error.WriteLine("Git synchronization FAILED: $($_.Exception.Message)")
    [Console]::Error.WriteLine('Review Git output. Any completed local commit is retained. No automatic conflict resolution, reset, or force-push is attempted.')
    if ($RebaseBeforePush) {
        [Console]::Error.WriteLine('If the requested pull --rebase stopped on a conflict, resolve it and run git rebase --continue before retrying synchronization.')
    }
} finally {
    if ($locationPushed) {
        Pop-Location
    }
    if (-not $NoPause) {
        Read-Host 'Press Enter to close' | Out-Null
    }
}

exit $syncExit
