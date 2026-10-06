# Active verification and research tooling

Current mode: **active-development**, 11/20 proof gates complete. Run the folder-local paper BAT with `--no-pause`; it supports any caller directory.

The runner verifies all retained files and production/verification Lean modules, full root-import coverage, immutable source pins, parent configuration, identical dependency revisions, the original node-63 synchronization BAT, JSON/checklist/diagram status agreement, TeX labels and local links. It builds all implemented modules and executes exact-type source regressions and the exhaustive transitive axiom audit. Nonzero exits, Lean errors/warnings and tactic suggestions fail the run. A development PASS explicitly leaves uncompleted source gates open.

`verify_scaffold.py` retains its filename but validates the active package. `scaffold.json` classifies all retained artifacts and modules. The original source verifier and its eight regression cases remain mandatory. Logs are generated under `logs/`; the foundation BAT is a separate sequential gate.

`reproduce_author_code.py` independently replays the unchanged AFE2 program, reporting numerical observations only. Source-label, local-reuse, template-inventory and upstream-snapshot JSON retain their dated provenance. Existing Lean APIs must be inspected before duplicating foundations.

The owner-operated `../push_to_github.bat` is unchanged. Verification never stages, commits, pushes or invokes synchronization. Source hashes and canonical-LF hashes retain their original purposes.

The current AFE1 development contains 87 retained files, twenty-one production modules and two verification modules. All are covered by the exact inventory and root import checks; the historical setup inventory above remains a dated record. The public N=0 and general-N general-endpoint and half-integer consumers are mandatory regressions. No additional gate has been closed.

Current reflection/Lemma-7 development: 89 retained files, twenty-three production modules and two verification modules. Both new modules are classified and root-imported; 6/20 gates remain accepted.

Current digamma development: 90 retained files, twenty-four production modules and two verification modules. GammaDigammaReal is classified and root-imported; 6/20 gates remain accepted.

Current second-order AFE scope: 192 retained files, 126 production modules, two verification modules and 290 semantic consumers; 11/20 accepted gates. Exact current-checkout verification is recorded in the Reproduction Manifest.
