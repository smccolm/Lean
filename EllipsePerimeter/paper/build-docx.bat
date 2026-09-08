@echo off
setlocal enabledelayedexpansion

set "PREFIX=Ellipse Perimeter"
set "EXT=.docx"

if "%~1"=="" (
  set "INPUT=input.md"
) else (
  set "INPUT=%~1"
)

if not exist "%INPUT%" (
  echo Missing input file: "%INPUT%"
  echo.
  echo Usage examples:
  echo   build-docx.bat
  echo   build-docx.bat "input v1.md"
  echo   build-docx.bat "input v2.md"
  exit /b 1
)

set /a MAX=0

for %%F in ("%PREFIX% v*%EXT%") do (
  if exist "%%~fF" (
    set "STEM=%%~nF"
    set "NUM=!STEM:%PREFIX% v=!"
    set /a TESTNUM=!NUM! >nul 2>nul
    if !TESTNUM! GTR !MAX! set /a MAX=!TESTNUM!
  )
)

set /a NEXT=MAX+1
set "OUTPUT=%PREFIX% v%NEXT%%EXT%"

echo Input:
echo   "%INPUT%"
echo Output:
echo   "%OUTPUT%"
echo.

pandoc -f markdown+tex_math_dollars+tex_math_single_backslash -t docx "%INPUT%" -o "%OUTPUT%"

if errorlevel 1 (
  echo Pandoc failed.
  exit /b 1
)

echo Built "%OUTPUT%"