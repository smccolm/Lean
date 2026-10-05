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
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\run_dong_wang_wang_zhang_build.ps1"
set "BUILD_EXIT=%ERRORLEVEL%"
if "%NO_PAUSE%"=="0" pause
exit /b %BUILD_EXIT%
:usage
echo Usage: run_dong_wang_wang_zhang_build.bat [--no-pause]
echo This entry point verifies the active development package, not completion of the paper.
exit /b 2
