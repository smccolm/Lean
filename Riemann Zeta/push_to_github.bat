@echo off
setlocal EnableExtensions DisableDelayedExpansion

echo ====================================================================
echo  Lean Workspace - complete repository sync to GitHub
echo ====================================================================
echo.

set "SCRIPT_DIR=%~dp0"
set "NO_PAUSE=0"
if /I "%~1"=="--no-pause" (
  set "NO_PAUSE=1"
  shift
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
if not defined COMMIT_MESSAGE (
  set "COMMIT_MESSAGE=Rename post-GM research program and files to Prime Shell"
  set /p "COMMIT_MESSAGE=Commit message [%COMMIT_MESSAGE%]: "
)
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

:maybe_pause
if "%NO_PAUSE%"=="0" pause
exit /b 0
