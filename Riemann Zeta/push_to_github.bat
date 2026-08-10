@echo off
echo ====================================================================
echo  Lean Workspace - GitHub Push Script (https://github.com/smccolm/Lean)
echo ====================================================================
echo.
echo Staging workspace files...
git add .

echo Committing workspace progress...
git commit -m "Complete #18 Appendix C contour coverage proof"

echo.
echo Pushing to GitHub (origin/main --force)...
git push origin main --force

echo.
echo ====================================================================
echo  Git Sync Completed Successfully!
echo ====================================================================
pause
