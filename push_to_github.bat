@echo off
echo ====================================================================
echo  Lean Workspace - GitHub Push Script (https://github.com/smccolm/Lean)
echo ====================================================================
echo.
echo Staging all recent workspace files, Lean code, and logs...
git add .

echo Committing workspace progress...
git commit -m "Workspace update: Main README, Compacted Graphs, visualizer, and project logs"

echo.
echo Pushing to GitHub (origin/main)...
git push origin main

echo.
echo ====================================================================
echo  Git Sync Completed Successfully!
echo ====================================================================
pause
