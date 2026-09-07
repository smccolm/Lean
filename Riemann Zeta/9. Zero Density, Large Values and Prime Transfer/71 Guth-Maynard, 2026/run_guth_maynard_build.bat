@echo off
setlocal EnableExtensions
cd /d "%~dp0"

if not defined ELAN_HOME set "ELAN_HOME=%USERPROFILE%\.elan"

call "..\..\run_lake_build.bat" %*
exit /b %ERRORLEVEL%
