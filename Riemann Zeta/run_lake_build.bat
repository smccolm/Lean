@echo off
setlocal EnableExtensions

rem Thin Windows wrapper around the platform-neutral canonical verifier.
cd /d "%~dp0"

set "LAKE_EXE="
for /f "delims=" %%I in ('where lake.exe 2^>nul') do if not defined LAKE_EXE set "LAKE_EXE=%%I"
if not defined LAKE_EXE if exist "%USERPROFILE%\.elan\bin\lake.exe" set "LAKE_EXE=%USERPROFILE%\.elan\bin\lake.exe"
if not defined LAKE_EXE (
  echo ERROR: lake.exe was not found on PATH or under %%USERPROFILE%%\.elan\bin.
  echo Install Elan and the toolchain pinned by lean-toolchain, then retry.
  exit /b 1
)

set "VERIFY_MODE=development"
set "NO_PAUSE=0"
for %%A in (%*) do (
  if /I "%%~A"=="--release" set "VERIFY_MODE=release"
  if /I "%%~A"=="--no-pause" set "NO_PAUSE=1"
)

powershell -NoProfile -ExecutionPolicy Bypass -File "scripts\verify_release.ps1" -Mode "%VERIFY_MODE%"
set "VERIFY_EXIT=%ERRORLEVEL%"

if "%NO_PAUSE%"=="0" (
  echo.
  pause
)

exit /b %VERIFY_EXIT%
