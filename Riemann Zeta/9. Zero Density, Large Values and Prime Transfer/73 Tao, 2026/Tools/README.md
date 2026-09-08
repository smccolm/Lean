# Tao 2026 build tools

`run_tao_build.ps1` verifies the pinned Tao source artifacts, raw Mermaid
contract, Lean and Mathlib pins, direct production-root coverage, forbidden
proof shortcuts, and a warning-free build. It currently certifies only the
initial source-definition milestone; it is not yet the final proof-release
verifier described by `Tao Goal Prompt.md`.
