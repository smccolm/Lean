# Tooling plan

The planning baseline includes the human-facing build runner. Until a unified
Lean package is installed, it verifies the scaffold inventory, pinned sources,
and forbidden-shortcut scan, then prints `PLANNING SCAFFOLD ONLY`. It must not
describe that result as a Lean build or theorem audit.

Planned tools:

- `verify_sources.ps1` -- recompute `Sources/SHA256SUMS.txt`, check archive
  commit metadata, and fail on missing/unlisted files;
- `reproduce_paper_time.py` -- invoke pinned ANTEDB functions for the 2025
  outputs and serialize exact rational results;
- `emit_certificates.py` -- convert exact rational witnesses to deterministic
  Lean data, never theorem declarations;
- `check_generated.ps1` -- regenerate into a temporary directory and fail on
  any diff;
- `run_tao_trudgian_yang_build.ps1` -- scaffold verifier now; automatically becomes the
  warning-failing Lake build, semantic-regression, axiom-audit, integrity, and
  pin orchestrator when `Extension/lakefile.toml` and `lean-toolchain` are
  installed together; and
- `run_tao_trudgian_yang_build.bat` -- human-facing wrapper at the project root, with
  `--no-pause` support for agents and CI.

Every tool must print the exact input pins and preserve complete stdout/stderr
in the reproduction log. A tool exit code is not proof evidence unless its
output is consumed by a Lean kernel-checked certificate theorem.
