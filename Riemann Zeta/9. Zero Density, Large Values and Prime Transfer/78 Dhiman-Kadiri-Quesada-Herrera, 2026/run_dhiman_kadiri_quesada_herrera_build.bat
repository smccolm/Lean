@echo off
setlocal EnableExtensions
set "NO_PAUSE=0"
if "%~1"=="" goto :run
if /I not "%~1"=="--no-pause" goto :usage
if not "%~2"=="" goto :usage
set "NO_PAUSE=1"
:run
cd /d "%~dp0"
if errorlevel 1 exit /b 1
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\run_dhiman_kadiri_quesada_herrera_build.ps1"
set "BUILD_EXIT=%ERRORLEVEL%"
if "%NO_PAUSE%"=="0" pause
exit /b %BUILD_EXIT%
:usage
echo Usage: run_dhiman_kadiri_quesada_herrera_build.bat [--no-pause]
echo Verifies the active Lean package, source pins, proof gates and dependency audit.
exit /b 2
