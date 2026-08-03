@echo off
echo ====================================================================
echo  Lean Workspace - GitHub Push Script (https://github.com/smccolm/Lean)
echo ====================================================================
echo.
echo Staging workspace files...
git add .

echo Committing workspace progress...
git commit -m "Add lean_build_diag.cmd diagnostic runner for Reimann Zeta"

echo.
echo Pushing to GitHub (origin/main)...
git push origin main

echo.
echo ====================================================================
echo  Git Sync Completed Successfully!
echo ====================================================================
pause
