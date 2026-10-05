# Dhiman–Kadiri–Quesada-Herrera 2026: project scaffold

**PLANNING ONLY — GOAL INACTIVE — Lean conversion NOT STARTED. 0/20 proof gates complete.**
Research cutoff: **5 October 2026**, with live primary-source and GitHub checks recorded in [the snapshot](Tools/upstream_snapshot.json).

Natasha Dhiman, Habiba Kadiri and Emily Quesada-Herrera, *Explicit Exponential Sum Estimates and Approximate Functional Equations for the Zeta Function*, [arXiv:2609.00537v1](https://arxiv.org/abs/2609.00537v1), submitted 1 September 2026, 37 pages. The live arXiv history lists v1; the authors still list it as a preprint/current research work. No later revision, journal publication or author erratum was found in this survey. This is a bounded observation, not a guarantee about unindexed material.

The template follows every retained file/folder role in node 77. It reserves an independent future `DhimanKadiriQuesadaHerrera2026` package, preserves the completed local work, and includes the **unaltered node-63 `push_to_github.bat`**. No `.lean`, Lake package, import, dependency upgrade, goal activation, commit or push is part of this setup.

## Start here

1. [Goal Prompt](Dhiman-Kadiri-Quesada-Herrera%20Goal%20Prompt.md) — ready for a later explicit activation.
2. [Source Contract](Dhiman-Kadiri-Quesada-Herrera%20Source%20Contract.md) and [Errata](Dhiman-Kadiri-Quesada-Herrera%20Errata.md) — intended results and material source discrepancies.
3. [Checklist](Dhiman-Kadiri-Quesada-Herrera%20Checklist.md) and [Architecture](Dhiman-Kadiri-Quesada-Herrera%20Architecture.md) — twenty future proof/acceptance gates, all OPEN.
4. [Crosswalk](Dhiman-Kadiri-Quesada-Herrera%20Crosswalk.md) and [Dependencies](Dependencies/README.md) — exact local interfaces, mismatches and future import decisions.
5. [Sources](Dhiman-Kadiri-Quesada-Herrera%20Sources.md), [Computation Review](Dhiman-Kadiri-Quesada-Herrera%20Computation%20Review.md) and [Reproduction Manifest](Dhiman-Kadiri-Quesada-Herrera%20Reproduction%20Manifest.md) — dated research, source/code pins and evidence.
6. [Research Agenda](Dhiman-Kadiri-Quesada-Herrera%20Research%20Agenda.md) and [Template Inventory](Dhiman-Kadiri-Quesada-Herrera%20Template%20Inventory.md) — implementation order and complete adaptation accounting.

## Source review findings

Theorem 9 prints `1 < n` although its proof and Corollary 0.3 include `n=1`. Equation (5.2) interchanges the error branches relative to the proof and `AFE2.py`. Other sign, endpoint, general-N and numerical-certification questions are catalogued in Errata. Original PDF, TeX, bibliography, figures and both ancillary programs are retained byte-for-byte. Proposed corrections are explicitly provisional; no corrected mathematical theorem has been proved here.

`AFE2.py` ran unmodified under the recorded local Python/NumPy/SciPy versions and reproduced the displayed Table 1 values. Its floating-point maxima and rounded displays are **computational observations**, not certified bounds. `AFE1.sage` was inspected but not executed; SageMath 9.5 is not available in this environment.

## Verification and owner synchronization

```powershell
cmd /c run_dhiman_kadiri_quesada_herrera_build.bat --no-pause
```

The current runner verifies scaffold inventory, source hashes, unchanged parent pins, inactive-goal status, all-open proof gates, local links, source-label anchors, and the exact node-63 synchronization-script bytes. It refuses any Lean/package files in this planning scaffold. Success says **SCAFFOLD PASS — LEAN CONVERSION NOT STARTED**, never Lean proof PASS. It logs under `logs/`, returns nonzero on failure, and supports double-click pause.

The folder-local `push_to_github.bat` retains node 63's owner-supplied message, repository-wide staging, pull/rebase and push workflow. It is present for the owner to run separately; verification never invokes it. It stages the whole Git repository, not only 78. No recovery-record maintenance is required.
