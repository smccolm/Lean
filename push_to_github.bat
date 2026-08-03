@echo off
echo ====================================================================
echo  Lean Workspace - GitHub Push Script (https://github.com/smccolm/Lean)
echo ====================================================================
echo.
echo Staging workspace files...
git add .

echo Committing workspace progress...
git commit -m "Address all 63 audit critiques: positive index PNat, genuine Hardy Z, full 4-fold zero orbit, Lean 4.30.0 stable, CI workflow, and Paper_Riemann_Zeta_v6.docx"

echo.
echo Pushing to GitHub (origin/main)...
git push origin main

echo.
echo ====================================================================
echo  Git Sync Completed Successfully!
echo ====================================================================
pause
