@echo off
echo ====================================================================
echo  Lean Workspace - GitHub Push Script (https://github.com/smccolm/Lean)
echo ====================================================================
echo.
echo Staging workspace files...
git add .

echo Committing workspace progress...
git commit -m "Formalize source-uniform DFI Equation 28 to 29 Mellin bounds"

echo.
echo Pushing to GitHub (origin/main --force)...
git push origin main --force

echo.
echo ====================================================================
echo  Git Sync Completed Successfully!
echo ====================================================================
pause
