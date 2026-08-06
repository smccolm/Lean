@echo off
lake build > latest_build_output.txt 2>&1
echo Exit Code: %errorlevel% >> latest_build_output.txt
