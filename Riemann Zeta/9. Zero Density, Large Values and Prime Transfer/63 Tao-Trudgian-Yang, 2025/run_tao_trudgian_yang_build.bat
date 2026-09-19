@echo off
setlocal
cd /d "%~dp0"

powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\run_tao_trudgian_yang_build.ps1"
set "BUILD_EXIT=%ERRORLEVEL%"

if /I not "%~1"=="--no-pause" pause
exit /b %BUILD_EXIT%

