@echo off
setlocal
cd /d "%~dp0"

for /f "delims=" %%R in ('git rev-parse --show-toplevel 2^>nul') do set "REPO_ROOT=%%R"
if not defined REPO_ROOT (
  echo ERROR: Could not find the Git repository root.
  pause
  exit /b 1
)

rem Keep this message current: update it periodically to describe the work being pushed.
set "DEFAULT_COMMIT_MESSAGE=Advance Prime Shell research"
set "COMMIT_MESSAGE=%~1"
if not defined COMMIT_MESSAGE set /p "COMMIT_MESSAGE=Commit message [%DEFAULT_COMMIT_MESSAGE%]: "
if not defined COMMIT_MESSAGE set "COMMIT_MESSAGE=%DEFAULT_COMMIT_MESSAGE%"

git -C "%REPO_ROOT%" add -A
if errorlevel 1 goto :fail

git -C "%REPO_ROOT%" diff --cached --quiet
if errorlevel 1 (
  git -C "%REPO_ROOT%" commit -m "%COMMIT_MESSAGE%"
  if errorlevel 1 goto :fail
) else (
  echo No new changes to commit.
)

git -C "%REPO_ROOT%" push origin HEAD:main
if errorlevel 1 goto :fail

echo.
echo Pushed to origin/main.
pause
exit /b 0

:fail
echo.
echo Push failed. Review the Git output above.
pause
exit /b 1
