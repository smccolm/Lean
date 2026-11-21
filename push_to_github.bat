@echo off
setlocal EnableExtensions DisableDelayedExpansion

echo ====================================================================
echo  Lean Workspace - complete repository sync to GitHub
echo ====================================================================
echo.

set "SCRIPT_DIR=%~dp0"
set "NO_PAUSE=0"
set "REPAIR_SCRATCH=0"
set "LEAN_SCRATCH_DB=.scratch/dubon-alpoge-20261121/headers.sqlite"
set "REPO_ROOT="
set "CURRENT_BRANCH="

:read_options
if /I "%~1"=="--no-pause" (
  set "NO_PAUSE=1"
  shift /1
  goto read_options
)
if /I "%~1"=="--repair-scratch" (
  set "REPAIR_SCRATCH=1"
  shift /1
  goto read_options
)

cd /d "%SCRIPT_DIR%"
if errorlevel 1 (
  echo ERROR: Could not change to the directory containing this script.
  call :maybe_pause
  exit /b 1
)

for /f "delims=" %%I in ('git rev-parse --show-toplevel 2^>nul') do set "REPO_ROOT=%%I"
if not defined REPO_ROOT (
  echo ERROR: This script is not inside a Git repository.
  call :maybe_pause
  exit /b 1
)
cd /d "%REPO_ROOT%"
if errorlevel 1 (
  echo ERROR: Could not change to repository root "%REPO_ROOT%".
  call :maybe_pause
  exit /b 1
)

for /f "delims=" %%I in ('git branch --show-current 2^>nul') do set "CURRENT_BRANCH=%%I"
if errorlevel 1 (
  echo ERROR: Could not determine the current branch.
  call :maybe_pause
  exit /b 1
)
if /I not "%CURRENT_BRANCH%"=="main" (
  echo ERROR: Refusing to commit or push from branch "%CURRENT_BRANCH%"; expected "main".
  call :maybe_pause
  exit /b 1
)

if "%REPAIR_SCRATCH%"=="1" (
  python -c "import pathlib,sys; p=pathlib.Path(sys.argv[1]); exec(compile(p.read_bytes().split(b'\n# PYTHON REPAIR PAYLOAD',1)[1],str(p),'exec'))" "%~f0"
  if errorlevel 1 goto failed
)

git check-ignore -q --no-index -- "%LEAN_SCRATCH_DB%"
if errorlevel 2 goto failed
if not errorlevel 1 goto scratch_ignored
>>".gitignore" echo(
>>".gitignore" echo /%LEAN_SCRATCH_DB%
git check-ignore -q --no-index -- "%LEAN_SCRATCH_DB%"
if errorlevel 1 (
  echo ERROR: Could not exclude the scratch database. Check the repository ignore rules.
  goto failed
)

:scratch_ignored
git rm --quiet --force --cached --ignore-unmatch -- "%LEAN_SCRATCH_DB%"
if errorlevel 1 goto failed

echo Staging repository-wide changes from "%REPO_ROOT%"...
echo This includes tracked changes, deletions, and all untracked non-ignored files.
git add -A
if errorlevel 1 (
  echo ERROR: git add -A failed. Nothing was pushed.
  call :maybe_pause
  exit /b 1
)

git diff --cached --quiet
if not errorlevel 1 (
  echo No staged changes; skipping the commit step.
  goto verify_complete_commit
)
if errorlevel 2 (
  echo ERROR: Could not inspect the staged changes. Nothing was pushed.
  call :maybe_pause
  exit /b 1
)

set "COMMIT_MESSAGE=%~1"
if defined COMMIT_MESSAGE goto validate_message
set "COMMIT_MESSAGE=Rename post-GM research program and files to Prime Shell"
set /p "COMMIT_MESSAGE=Commit message [%COMMIT_MESSAGE%]: "
:validate_message
set "PUSH_COMMIT_MESSAGE=%COMMIT_MESSAGE%"
powershell -NoProfile -Command "if ([string]::IsNullOrWhiteSpace($env:PUSH_COMMIT_MESSAGE)) { exit 1 } else { exit 0 }"
if errorlevel 1 (
  echo ERROR: Commit message must not be empty or whitespace.
  call :maybe_pause
  exit /b 1
)

echo Committing reviewed changes...
git commit -m "%COMMIT_MESSAGE%"
if errorlevel 1 (
  echo ERROR: git commit failed. Nothing was pushed.
  call :maybe_pause
  exit /b 1
)

:verify_complete_commit
set "REMAINING_CHANGE="
for /f "delims=" %%S in ('git status --porcelain --untracked-files^=all') do set "REMAINING_CHANGE=%%S"
if defined REMAINING_CHANGE (
  echo ERROR: Non-ignored repository changes remain after the commit.
  echo Nothing was pushed; review git status and rerun this script.
  git status --short
  call :maybe_pause
  exit /b 1
)

echo Pushing main to origin without force...
git push origin main
if errorlevel 1 (
  echo ERROR: git push origin main failed.
  echo If GitHub named %LEAN_SCRATCH_DB%, rerun with --repair-scratch.
  call :maybe_pause
  exit /b 1
)

echo Pushing every local tag to origin without force...
git push origin --tags
if errorlevel 1 (
  echo ERROR: One or more local tags could not be pushed.
  call :maybe_pause
  exit /b 1
)

echo.
echo ====================================================================
echo  Git sync completed: main and all local tags are on origin.
echo ====================================================================
echo No build was run. GitHub CI, if triggered, runs asynchronously and
echo is not checked or awaited by this script.
call :maybe_pause
exit /b 0

:failed
call :maybe_pause
exit /b 1

:maybe_pause
if "%NO_PAUSE%"=="0" pause
exit /b 0

# PYTHON REPAIR PAYLOAD
# Run by the --repair-scratch option. Use a separate index to edit commit trees.
import functools
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def git(*args, data=None, index=None):
    env = None if index is None else dict(os.environ, GIT_INDEX_FILE=str(index))
    return subprocess.run(
        ["git", "--no-replace-objects", *args],
        input=data, stdout=subprocess.PIPE, env=env, check=True
    ).stdout


def repair():
    path = os.environ["LEAN_SCRATCH_DB"]
    branch = "refs/heads/main"
    upstream = "refs/remotes/origin/main"
    if git("symbolic-ref", "HEAD").strip() != branch.encode():
        raise ValueError("Check out main before running the repair.")

    git("fetch", "--no-tags", "origin", "refs/heads/main:" + upstream)
    base = git("rev-parse", upstream).strip().decode("ascii")
    old = git("rev-parse", branch).strip().decode("ascii")
    try:
        git("merge-base", "--is-ancestor", base, old)
    except subprocess.CalledProcessError:
        raise ValueError("Local main must contain the fetched origin/main. Review git status -sb.")

    # Rewrite parents before children. Published commits and all other refs are excluded.
    commits = git("rev-list", "--reverse", "--topo-order", base + ".." + old).splitlines()
    rewritten = {}
    roots = []
    with tempfile.TemporaryDirectory(prefix="lean-push-") as tmp:
        index = Path(tmp).resolve() / "index"

        @functools.lru_cache(maxsize=None)
        def clean_tree(tree):
            entry = git("ls-tree", "-z", tree, "--", path)
            if not entry:
                return tree
            if entry.split(b" ", 2)[1] != b"blob":
                raise ValueError("The database path refers to an unexpected object. Inspect it before retrying.")
            git("read-tree", tree, index=index)
            git("update-index", "--force-remove", "--", path, index=index)
            return git("write-tree", index=index).strip()

        for commit in commits:
            raw = git("cat-file", "commit", commit)
            header, separator, message = raw.partition(b"\n\n")
            lines = header.split(b"\n")
            changed_headers = []
            parent_changed = False
            for line in lines:
                key, space, value = line.partition(b" ")
                if key == b"tree":
                    value = clean_tree(value)
                elif key == b"parent" and value in rewritten:
                    value = rewritten[value]
                    parent_changed = True
                changed_headers.append(key + space + value)
            if changed_headers == lines:
                continue
            if any(line.startswith((b"gpgsig ", b"gpgsig-", b"mergetag ")) for line in lines):
                raise ValueError("Commit " + commit.decode() + " contains a signature or merge tag. Repair stopped before moving main.")
            if not parent_changed:
                roots.append(commit)
            updated = b"\n".join(changed_headers) + separator + message
            rewritten[commit] = git("hash-object", "-w", "-t", "commit", "--stdin", data=updated).strip()

    if not rewritten:
        print("No unpublished commit needs repair.")
        return

    affected_tags = set()
    for root in roots:
        affected_tags.update(git("tag", "--contains", root).splitlines())
    if affected_tags:
        print("These tags still reference the original history and may be rejected by GitHub:")
        for tag in sorted(affected_tags):
            print("  " + os.fsdecode(tag))

    new = rewritten[old.encode()].decode("ascii")
    backup = "backup/before-scratch-repair-" + old
    # Both refs move together. Concurrent updates to main or origin/main cancel the repair.
    transaction = (
        f"verify {upstream} {base}\n"
        f"create refs/heads/{backup} {old}\n"
        f"update {branch} {new} {old}\n"
    )
    git("update-ref", "-m", "remove local scratch database from unpublished main",
        "--stdin", data=transaction.encode("ascii"))
    print(f"Repaired {len(rewritten)} unpublished commit(s). Local backup: {backup}")


try:
    repair()
except (OSError, ValueError, subprocess.CalledProcessError) as error:
    print("ERROR: " + str(error), file=sys.stderr)
    sys.exit(1)
