# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `definitions-0.1`. It reproduces the
source identities, pinned build environment, and initial source definitions.
It is not a Tao theorem release manifest.

## Pinned source

- Paper: Terence Tao, *Products of consecutive integers with unusual anatomy*.
- arXiv identifier: `2603.27990v2`.
- PDF and TeX archive hashes: `Sources/SHA256SUMS.txt`.
- Provenance and download URLs: `Sources/PINS.md`.

## Lean package

- Package directory: `Extension/`.
- Package/library name: `Tao2026`.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Production modules: `Anatomy`, `Intervals`, `Asymptotics`, and `Counting`.
- Proved content: definition-interface lemmas only; no paper theorem.

## Reproduction command

From this node directory:

```powershell
cmd /c run_tao_build.bat --no-pause
```

The command verifies:

1. required project files;
2. both source artifact hashes;
3. the raw-only Mermaid architecture contract;
4. the exact Lean and Mathlib pins;
5. direct production-root import coverage and forbidden-shortcut absence; and
6. the warning-free `Tao2026` build.

The runner emits no persistent log. Console success is evidence only for the
checkout on which it was run.

## Not yet reproducible

The source crosswalk now records the initial definitions and main targets.
There is no frozen node-71/node-74 dependency closure, public theorem endpoint,
complete axiom audit, or formal proof release to reproduce. Those omissions
remain explicit until the active project supplies them.
