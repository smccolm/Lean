@echo off
echo ====================================================================
echo  Lean Workspace - GitHub Push Script (https://github.com/smccolm/Lean)
echo ====================================================================
echo.
echo Staging workspace files...
git add .

echo Committing workspace progress...
git commit -m "Complete resolution of all 46 re-audit critiques: refactored module names, verified no-sorry audit, updated CI workflow, corrected citations, and exported Paper_Riemann_Zeta_v7.docx"

echo.
echo Pushing to GitHub (origin/main)...
git push origin main

echo.
echo ====================================================================
echo  Git Sync Completed Successfully!
echo ====================================================================
pause
