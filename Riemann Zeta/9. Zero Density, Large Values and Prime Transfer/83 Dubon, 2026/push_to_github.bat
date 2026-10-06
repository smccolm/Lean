@echo off
setlocal
cd /d "%~dp0"

for /f "delims=" %%R in ('git rev-parse --show-toplevel 2^>nul') do set "REPO_ROOT=%%R"
if not defined REPO_ROOT (
  echo ERROR: Could not find the Git repository root.
  pause
  exit /b 1
)

set "COMMIT_MESSAGE=%~1"
if not defined COMMIT_MESSAGE set /p "COMMIT_MESSAGE=Commit message: "
if not defined COMMIT_MESSAGE (
  echo ERROR: Commit message cannot be empty.
  pause
  exit /b 1
)

echo.
echo Staging changes...
git -C "%REPO_ROOT%" add -A
if errorlevel 1 goto :fail

git -C "%REPO_ROOT%" diff --cached --quiet
if errorlevel 1 (
  echo.
  echo Committing changes...
  git -C "%REPO_ROOT%" commit -m "%COMMIT_MESSAGE%"
  if errorlevel 1 goto :fail
) else (
  echo No new changes to commit.
)

echo.
echo Updating local main from origin/main...
git -C "%REPO_ROOT%" pull --rebase origin main
if errorlevel 1 goto :rebasefail

echo.
echo Pushing to origin/main...
git -C "%REPO_ROOT%" push origin main
if errorlevel 1 goto :fail

echo.
echo ============================================================
echo Git sync completed successfully.
echo ============================================================
pause
exit /b 0

:rebasefail
echo.
echo ============================================================
echo REBASE FAILED.
echo Your commit is safe, but Git found a conflict while syncing.
echo Resolve the conflict, then run:
echo.
echo   git -C "%REPO_ROOT%" rebase --continue
echo.
echo After the rebase finishes, run this BAT again.
echo ============================================================
pause
exit /b 1

:fail
echo.
echo ============================================================
echo Git sync failed. Review the Git output above.
echo ============================================================
pause
exit /b 1