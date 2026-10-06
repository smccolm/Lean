@echo off
setlocal
cd /d "%~dp0"
if errorlevel 1 exit /b 1
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\run_dubon_verification.ps1"
set "DUBON_EXIT=%ERRORLEVEL%"
if /i not "%~1"=="--no-pause" pause
exit /b %DUBON_EXIT%
