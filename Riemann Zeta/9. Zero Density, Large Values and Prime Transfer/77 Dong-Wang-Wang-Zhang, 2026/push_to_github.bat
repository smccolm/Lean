@echo off
setlocal EnableExtensions
cd /d "%~dp0"
if errorlevel 1 exit /b 1
rem Preserve the owner's pull --rebase workflow; the helper checks every Git exit.
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\push_to_github.ps1" -RebaseBeforePush %*
set "SYNC_EXIT=%ERRORLEVEL%"
exit /b %SYNC_EXIT%
