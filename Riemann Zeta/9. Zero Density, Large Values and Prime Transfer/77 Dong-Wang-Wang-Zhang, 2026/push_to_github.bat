@echo off
setlocal EnableExtensions DisableDelayedExpansion
rem Owner-only interface. This stages changes across the entire Git repository.
rem Usage: push_to_github.bat ["Commit message"] [-NoPause]
powershell.exe -NoProfile -ExecutionPolicy Bypass -File "%~dp0Tools\push_to_github.ps1" %*
exit /b %ERRORLEVEL%
