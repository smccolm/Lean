@echo off
setlocal EnableExtensions

rem Always run from the directory containing this script.
cd /d "%~dp0"

if not exist "lakefile.toml" if not exist "lakefile.lean" (
  echo ERROR: No Lake project file was found in:
  echo   %CD%
  pause
  exit /b 1
)

rem Resolve the actual executable instead of assuming that the current
rem USERPROFILE owns the Elan installation.
set "LAKE="
for /f "delims=" %%I in ('where lake.exe 2^>nul') do if not defined LAKE set "LAKE=%%I"
if not defined LAKE if exist "%USERPROFILE%\.elan\bin\lake.exe" set "LAKE=%USERPROFILE%\.elan\bin\lake.exe"

if not defined LAKE (
  echo ERROR: lake.exe was not found on PATH or under %%USERPROFILE%%\.elan\bin.
  echo Install Elan and the toolchain named in lean-toolchain, then run this file again.
  pause
  exit /b 1
)

rem If this Lake belongs to Elan, infer ELAN_HOME from ...\.elan\bin\lake.exe.
if not defined ELAN_HOME (
  for %%I in ("%LAKE%") do for %%J in ("%%~dpI..") do if exist "%%~fJ\toolchains" set "ELAN_HOME=%%~fJ"
)

if not exist "logs" mkdir "logs"
for /f %%I in ('powershell -NoProfile -Command "Get-Date -Format yyyyMMdd_HHmmss"') do set "TS=%%I"

set "LOG=%CD%\logs\overall_proof_%TS%.log"
set "STEP_LOG=%TEMP%\riemann_zeta_step_%RANDOM%_%RANDOM%.log"
set "FAILED=0"

(
  echo ============================================================
  echo RIEMANN ZETA - OVERALL LEAN VERIFICATION
  echo ============================================================
  echo Started: %DATE% %TIME%
  echo Project: %CD%
  echo Toolchain:
  type "lean-toolchain"
  echo.
  echo Lean verifies proofs by compiling their declarations and checking
  echo their dependencies in the kernel. This runner cannot make an
  echo unproved theorem true; it fails when a production module, retained
  echo example, audit, proof-integrity gate, or zero-warning gate fails.
  echo.
) > "%LOG%"

echo ============================================================
echo RIEMANN ZETA - OVERALL LEAN VERIFICATION
echo ============================================================
echo Log: %LOG%
echo.

call :run_lake "1/5 Default project build" build RiemannZeta
call :run_lake "2/5 Explicit production-module coverage" build RiemannZeta.GuthMaynard.DyadicTransfer RiemannZeta.GuthMaynard.CentralTypeI RiemannZeta.GuthMaynard.HalaszMontgomery RiemannZeta.GuthMaynard.Decoupling RiemannZeta.GuthMaynard.LargeValues
call :run_lake "3/5 Retained example: complex exponential" env lean TestExp.lean
call :run_lake "4/5 Retained example: separated selection" env lean test_separated.lean
call :run_lake "5/5 Current Lean audit module" env lean RiemannZeta\Audit.lean

echo.
echo [INTEGRITY] Repository-wide prohibited-proof scan
echo [INTEGRITY] Repository-wide prohibited-proof scan>> "%LOG%"

where rg.exe >nul 2>&1
if errorlevel 1 (
  echo FAIL: rg.exe is required for the repository-wide integrity scan.
  echo FAIL: rg.exe is required for the repository-wide integrity scan.>> "%LOG%"
  set "FAILED=1"
) else (
  call :scan_sorry
  call :scan_axioms
  call :scan_unsafe
  call :scan_audit_quality
)

del "%STEP_LOG%" >nul 2>&1

echo.
echo ============================================================
echo FINAL RESULT
echo ============================================================
echo.>> "%LOG%"
echo ============================================================>> "%LOG%"
echo FINAL RESULT>> "%LOG%"
echo ============================================================>> "%LOG%"

if "%FAILED%"=="0" (
  echo PASS: Every requested build, audit, and integrity gate passed.
  echo PASS: Every requested build, audit, and integrity gate passed.>> "%LOG%"
  echo This means Lean accepted the declarations currently present, emitted no warnings, and the scans found no forbidden proof shortcuts.
  echo This means Lean accepted the declarations currently present, emitted no warnings, and the scans found no forbidden proof shortcuts.>> "%LOG%"
  set "EXIT_CODE=0"
) else (
  echo FAIL: The repository does not currently pass overall proof verification.
  echo FAIL: The repository does not currently pass overall proof verification.>> "%LOG%"
  echo Read the failed stages and integrity matches in the log. No overall-proof claim is justified yet.
  echo Read the failed stages and integrity matches in the log. No overall-proof claim is justified yet.>> "%LOG%"
  set "EXIT_CODE=1"
)

echo Finished: %DATE% %TIME%
echo Finished: %DATE% %TIME%>> "%LOG%"
echo Log saved to: %LOG%

if /I not "%~1"=="--no-pause" (
  echo.
  pause
)

exit /b %EXIT_CODE%

:run_lake
set "STEP_NAME=%~1"
echo.
echo [%STEP_NAME%]
echo.>> "%LOG%"
echo [%STEP_NAME%]>> "%LOG%"

"%LAKE%" %2 %3 %4 %5 %6 > "%STEP_LOG%" 2>&1
set "STEP_EXIT=%ERRORLEVEL%"
type "%STEP_LOG%"
type "%STEP_LOG%" >> "%LOG%"

findstr /C:"warning:" "%STEP_LOG%" >nul 2>&1
set "WARNING_SCAN=%ERRORLEVEL%"

if "%STEP_EXIT%"=="0" (
  if "%WARNING_SCAN%"=="1" (
    echo PASS: %STEP_NAME% ^(zero Lean warnings^)
    echo PASS: %STEP_NAME% ^(zero Lean warnings^)>> "%LOG%"
  ) else if "%WARNING_SCAN%"=="0" (
    echo FAIL: %STEP_NAME% emitted Lean warnings despite exit 0.
    echo FAIL: %STEP_NAME% emitted Lean warnings despite exit 0.>> "%LOG%"
    set "FAILED=1"
  ) else (
    echo FAIL: warning detection failed for %STEP_NAME% ^(exit %WARNING_SCAN%^).
    echo FAIL: warning detection failed for %STEP_NAME% ^(exit %WARNING_SCAN%^).>> "%LOG%"
    set "FAILED=1"
  )
) else (
  echo FAIL: %STEP_NAME% ^(exit %STEP_EXIT%^)
  echo FAIL: %STEP_NAME% ^(exit %STEP_EXIT%^)>> "%LOG%"
  if "%WARNING_SCAN%"=="0" (
    echo FAIL: %STEP_NAME% also emitted Lean warnings.
    echo FAIL: %STEP_NAME% also emitted Lean warnings.>> "%LOG%"
  ) else if not "%WARNING_SCAN%"=="1" (
    echo FAIL: warning detection failed for %STEP_NAME% ^(exit %WARNING_SCAN%^).
    echo FAIL: warning detection failed for %STEP_NAME% ^(exit %WARNING_SCAN%^).>> "%LOG%"
  )
  set "FAILED=1"
)
exit /b 0

:scan_sorry
rg --no-ignore -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" . > "%STEP_LOG%" 2>&1
set "SCAN_EXIT=%ERRORLEVEL%"
if "%SCAN_EXIT%"=="1" (
  echo PASS: no sorry, admit, or sorryAx text found in Lean files.
  echo PASS: no sorry, admit, or sorryAx text found in Lean files.>> "%LOG%"
) else (
  type "%STEP_LOG%"
  type "%STEP_LOG%" >> "%LOG%"
  if "%SCAN_EXIT%"=="0" (
    echo FAIL: forbidden sorry/admit material remains.
    echo FAIL: forbidden sorry/admit material remains.>> "%LOG%"
  ) else (
    echo FAIL: the sorry/admit scan itself failed ^(exit %SCAN_EXIT%^).
    echo FAIL: the sorry/admit scan itself failed ^(exit %SCAN_EXIT%^).>> "%LOG%"
  )
  set "FAILED=1"
)
exit /b 0

:scan_axioms
rg --no-ignore -n "^\s*(axiom|constant)\b" -g "*.lean" . > "%STEP_LOG%" 2>&1
set "SCAN_EXIT=%ERRORLEVEL%"
if "%SCAN_EXIT%"=="1" (
  echo PASS: no project axiom or constant declarations found in Lean files.
  echo PASS: no project axiom or constant declarations found in Lean files.>> "%LOG%"
) else (
  type "%STEP_LOG%"
  type "%STEP_LOG%" >> "%LOG%"
  if "%SCAN_EXIT%"=="0" (
    echo FAIL: project axiom/constant declarations remain.
    echo FAIL: project axiom/constant declarations remain.>> "%LOG%"
  ) else (
    echo FAIL: the axiom scan itself failed ^(exit %SCAN_EXIT%^).
    echo FAIL: the axiom scan itself failed ^(exit %SCAN_EXIT%^).>> "%LOG%"
  )
  set "FAILED=1"
)
exit /b 0

:scan_unsafe
rg --no-ignore -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" . > "%STEP_LOG%" 2>&1
set "SCAN_EXIT=%ERRORLEVEL%"
if "%SCAN_EXIT%"=="1" (
  echo PASS: no prohibited unsafe proof bypass found in Lean files.
  echo PASS: no prohibited unsafe proof bypass found in Lean files.>> "%LOG%"
) else (
  type "%STEP_LOG%"
  type "%STEP_LOG%" >> "%LOG%"
  if "%SCAN_EXIT%"=="0" (
    echo FAIL: prohibited unsafe proof-bypass material remains.
    echo FAIL: prohibited unsafe proof-bypass material remains.>> "%LOG%"
  ) else (
    echo FAIL: the unsafe scan itself failed ^(exit %SCAN_EXIT%^).
    echo FAIL: the unsafe scan itself failed ^(exit %SCAN_EXIT%^).>> "%LOG%"
  )
  set "FAILED=1"
)
exit /b 0

:scan_audit_quality
rg -n "#print\s+axioms|collectAxioms|getAxioms" "RiemannZeta\Audit.lean" > "%STEP_LOG%" 2>&1
set "SCAN_EXIT=%ERRORLEVEL%"
if "%SCAN_EXIT%"=="0" (
  echo PASS: Audit.lean contains an explicit axiom-dependency inspection mechanism.
  echo PASS: Audit.lean contains an explicit axiom-dependency inspection mechanism.>> "%LOG%"
) else (
  if "%SCAN_EXIT%"=="1" (
    echo FAIL: Audit.lean does not inspect theorem axiom dependencies; executing it is not an axiom audit.
    echo FAIL: Audit.lean does not inspect theorem axiom dependencies; executing it is not an axiom audit.>> "%LOG%"
  ) else (
    type "%STEP_LOG%"
    type "%STEP_LOG%" >> "%LOG%"
    echo FAIL: the Audit.lean implementation scan failed ^(exit %SCAN_EXIT%^).
    echo FAIL: the Audit.lean implementation scan failed ^(exit %SCAN_EXIT%^).>> "%LOG%"
  )
  set "FAILED=1"
)
exit /b 0
