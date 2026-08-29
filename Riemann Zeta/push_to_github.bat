@echo off
setlocal EnableExtensions DisableDelayedExpansion

echo ====================================================================
echo  Lean Workspace - reviewed commit and push to origin/main
echo ====================================================================
echo.

for /f "delims=" %%I in ('git rev-parse --show-toplevel 2^>nul') do set "REPO_ROOT=%%I"
if not defined REPO_ROOT (
  echo ERROR: This script is not inside a Git repository.
  pause
  exit /b 1
)
cd /d "%REPO_ROOT%"
if errorlevel 1 (
  echo ERROR: Could not change to repository root "%REPO_ROOT%".
  pause
  exit /b 1
)

for /f "delims=" %%I in ('git branch --show-current 2^>nul') do set "CURRENT_BRANCH=%%I"
if errorlevel 1 (
  echo ERROR: Could not determine the current branch.
  pause
  exit /b 1
)
if /I not "%CURRENT_BRANCH%"=="main" (
  echo ERROR: Refusing to commit or push from branch "%CURRENT_BRANCH%"; expected "main".
  pause
  exit /b 1
)

set "COMMIT_MESSAGE=%~1"
if not defined COMMIT_MESSAGE (
  set "COMMIT_MESSAGE=Repair foundation CI resilience and release-tag publishing"
  set /p "COMMIT_MESSAGE=Commit message [%COMMIT_MESSAGE%]: "
)
set "PUSH_COMMIT_MESSAGE=%COMMIT_MESSAGE%"
powershell -NoProfile -Command "if ([string]::IsNullOrWhiteSpace($env:PUSH_COMMIT_MESSAGE)) { exit 1 } else { exit 0 }"
if errorlevel 1 (
  echo ERROR: Commit message must not be empty or whitespace.
  pause
  exit /b 1
)

echo Staging repository-wide changes from "%REPO_ROOT%"...
git add -A
if errorlevel 1 (
  echo ERROR: git add -A failed. Nothing was pushed.
  pause
  exit /b 1
)

git diff --cached --quiet
if not errorlevel 1 (
  echo No staged changes; skipping the commit step.
  goto push_main
)
if errorlevel 2 (
  echo ERROR: Could not inspect the staged changes. Nothing was pushed.
  pause
  exit /b 1
)

echo Committing reviewed changes...
git commit -m "%COMMIT_MESSAGE%"
if errorlevel 1 (
  echo ERROR: git commit failed. Nothing was pushed.
  pause
  exit /b 1
)

:push_main
echo Pushing main to origin without force...
git push origin main
if errorlevel 1 (
  echo ERROR: git push origin main failed.
  pause
  exit /b 1
)

echo Publishing reachable annotated GM foundation-freeze tags without force...
for /f "delims=" %%T in ('git tag --list "gm-foundation-*" --merged HEAD') do (
  call :push_foundation_tag "%%T"
  if errorlevel 1 goto foundation_tag_failed
)
goto foundation_tags_done

:foundation_tag_failed
echo ERROR: A GM foundation-freeze tag could not be published safely.
pause
exit /b 1

:foundation_tags_done

echo.
echo ====================================================================
echo  Git sync completed successfully, including reachable release tags.
echo ====================================================================
pause
exit /b 0

:push_foundation_tag
set "FOUNDATION_TAG=%~1"
set "FOUNDATION_TAG_TYPE="
for /f "delims=" %%Y in ('git cat-file -t "refs/tags/%FOUNDATION_TAG%" 2^>nul') do set "FOUNDATION_TAG_TYPE=%%Y"
if /I not "%FOUNDATION_TAG_TYPE%"=="tag" (
  echo ERROR: Refusing to publish lightweight or invalid tag "%FOUNDATION_TAG%".
  exit /b 1
)
echo Pushing annotated tag "%FOUNDATION_TAG%"...
git push origin "refs/tags/%FOUNDATION_TAG%:refs/tags/%FOUNDATION_TAG%"
if errorlevel 1 exit /b 1
exit /b 0
