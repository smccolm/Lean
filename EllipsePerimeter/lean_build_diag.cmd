@echo off
setlocal EnableExtensions

cd /d "%~dp0"

if not exist "lakefile.lean" if not exist "lakefile.toml" (
  echo I could not find lakefile.lean or lakefile.toml in:
  echo   %CD%
  exit /b 1
)

if not exist "logs" mkdir "logs"

for /f %%I in ('powershell -NoProfile -Command "(Get-Date).ToString(\"yyyyMMdd_HHmmss\")"') do set "TS=%%I"

set "LOGFILE=%CD%\logs\lean_build_%TS%.log"
set "RUNNER=%TEMP%\lean_diag_runner_%RANDOM%_%RANDOM%.cmd"

if "%~1"=="" (
  set "BUILD_CMD=lake build -v --log-level=trace --no-ansi"
  set "BUILD_LABEL=FULL_PROJECT"
) else (
  set "BUILD_CMD=lake build %~1 -v --log-level=trace --no-ansi"
  set "BUILD_LABEL=%~1"
)

(
  echo @echo off
  echo cd /d "%CD%"
  echo echo ==================================================
  echo echo LEAN DIAGNOSTIC BUILD LOG
  echo echo ==================================================
  echo echo Timestamp: %DATE% %TIME%
  echo echo ProjectRoot: %CD%
  echo echo BuildTarget: %BUILD_LABEL%
  echo echo.
  echo echo ===== where =====
  echo where.exe lean
  echo where.exe lake
  echo where.exe elan
  echo echo.
  echo echo ===== versions =====
  echo lean --version
  echo lake --version
  echo elan --version
  echo echo.
  echo echo ===== lean-toolchain =====
  echo if exist "lean-toolchain" ^(
  echo   type "lean-toolchain"
  echo ^) else ^(
  echo   echo lean-toolchain file not found
  echo ^)
  echo echo.
  echo echo ===== EllipsePerimeter.lean =====
  echo if exist "EllipsePerimeter.lean" ^(
  echo   type "EllipsePerimeter.lean"
  echo ^) else ^(
  echo   echo EllipsePerimeter.lean not found
  echo ^)
  echo.
  echo echo ===== EllipsePerimeter\Wallis.lean =====
  echo if exist "EllipsePerimeter\Wallis.lean" ^(
  echo   type "EllipsePerimeter\Wallis.lean"
  echo ^) else ^(
  echo   echo EllipsePerimeter\Wallis.lean not found
  echo ^)
  echo echo.
  echo echo ===== lake env =====
  echo lake env
  echo echo.
  echo echo ===== lake build =====
  echo %BUILD_CMD%
) > "%RUNNER%"

powershell -NoProfile -ExecutionPolicy Bypass -Command ^
  "& { cmd /c call '%RUNNER%' 2>&1 | Tee-Object -FilePath '%LOGFILE%'; exit $LASTEXITCODE }"

set "EXITCODE=%ERRORLEVEL%"
set "RESULT_LINE=The Lean build failed in a messy or incomplete way. Please send me the log file and a screenshot from VS Code."

if "%EXITCODE%"=="0" (
  set "RESULT_LINE=The Lean build finished successfully. Everything in the requested target was accepted."
) else (
  findstr /C:"error:" "%LOGFILE%" >nul 2>&1
  if not errorlevel 1 (
    set "RESULT_LINE=The Lean build failed, but the log file should be enough for me to diagnose it."
  )
)

(
  echo.
  echo ===== result =====
  echo ExitCode: %EXITCODE%
  echo LogFile: %LOGFILE%
  echo HumanResult: %RESULT_LINE%
) >> "%LOGFILE%"

echo.
echo Build complete.
echo %RESULT_LINE%
echo Log saved to:
echo %LOGFILE%

del "%RUNNER%" >nul 2>&1

exit /b %EXITCODE%