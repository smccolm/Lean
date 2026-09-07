@echo off
setlocal
cd /d "%~dp0"

powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\run_gafni_tao_build.ps1"
set "GT_EXIT=%ERRORLEVEL%"

if /I not "%~1"=="--no-pause" pause
exit /b %GT_EXIT%
