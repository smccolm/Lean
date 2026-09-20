# Tooling record

The human-facing build runner now verifies the unified Lean package, frozen
ANTEDB source ledger, source archive hashes, forbidden-shortcut policy,
semantic regressions, and dynamic transitive axiom audit. It writes a complete
timestamped log and supports `--no-pause`.

Installed and planned tools:

- `verify_sources.ps1` -- recompute `Sources/SHA256SUMS.txt`, check archive
  commit metadata, and fail on missing/unlisted files;
- `generate_certificates.py` -- installed standard-library extractor that
  verifies the paper-time archive hash, extracts the four new-pair
  coordinates, reconstructs the eight exact Bourgain lower-envelope pieces,
  extracts and sign-normalizes all nine energy-clause tables from the frozen
  blueprint, and deterministically emits their kernel-consumed rational data
  module;
- `reproduce_paper_time.py` -- future tool to invoke pinned ANTEDB functions for the 2025
  outputs and serialize exact rational results;
- `emit_certificates.py` -- future full conversion of exact rational witnesses to deterministic
  Lean data, never theorem declarations;
- deterministic regeneration/diff checking for the installed generated module
  is integrated directly into the principal runner;
- `run_tao_trudgian_yang_build.ps1` -- installed warning-failing Lake build,
  semantic-regression, axiom-audit, integrity, inventory, and pin orchestrator;
- `run_tao_trudgian_yang_build.bat` -- human-facing wrapper at the project root, with
  `--no-pause` support for agents and CI.

Every tool must print the exact input pins and preserve complete stdout/stderr
in the reproduction log. A tool exit code is not proof evidence unless its
output is consumed by a Lean kernel-checked certificate theorem.
