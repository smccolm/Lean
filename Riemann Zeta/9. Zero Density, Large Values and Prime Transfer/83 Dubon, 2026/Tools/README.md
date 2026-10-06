# Active verification and research tooling

**GOAL ACTIVE — 0/20 proof gates complete.** Run `../run_dubon_build.bat --no-pause`. The active verifier checks file/module coverage, exact pins, source labels and archive bytes, gate/document consistency, public source regressions and exhaustive transitive dependencies, then rejects any Lean diagnostic.

`verify_scaffold.py` retains its original filename and template-fixture support, but now validates the active package. `scaffold.json` classifies every retained file and production/verification module. `run_dubon_verification.ps1` builds the full package, explicitly builds and runs SemanticRegression and Audit, and logs each stage. DEVELOPMENT PASS certifies only the implemented scope; PROOF PASS requires all twenty accepted gates.

The original `verify_sources.ps1` and eight source-ledger fixtures are unchanged. `inspect_source_archive.py` compares both original source members without executing them. `test_scaffold.py` exercises inactive-state regressions and active module-classification failures. No fixture is a mathematical proof.

The dated research JSON files retain their provenance. Source labels, bibliography, local reuse, original Project-78 inventory, code-availability observation, upstream snapshots and download receipts remain available. No tool invokes the owner synchronization BAT or stages, commits or pushes changes.
