# Complete node-77 template inventory and adaptation

The inventory below records the historical setup boundary. The owner activated the goal on 5 October 2026; the active adaptation is recorded after this table.

Inspected on 5 October 2026 at Git checkout `baef1ac59f8ded380b91dda2b5a04a5468f798a8`. Every physical file beneath node 77 was enumerated and hashed: **199 files**, of which **87 retained files** are outside generated `.lake/`, `logs/` and Python caches. The retained roles are **16 root, 51 Extension, 12 Sources, 7 Tools and 1 Dependencies**. [Machine inventory](Tools/template_inventory.json) records every path, byte count, SHA-256, generated classification and text headings/import/declaration inventory. Text files were read for structural inspection; selected relevant theorem types/bodies were inspected in detail. This is not a new semantic audit of all node-77 proof terms.

| Every node-77 role | Node-78 treatment |
|---|---|
| README; Architecture; Checklist; Crosswalk; Goal Prompt; Reproduction Manifest; Research Agenda; Sources; Errata; Source Contract; Template Inventory | All eleven corresponding roles present with paper-specific content. Inactive status and all OPEN gates replace 77's completed state. No mathematical result or PASS claim copied. |
| `.gitattributes`, `.gitignore`, `.gitkeep` | Present; preserve archived bytes, normalize project text, ignore generated logs/caches, point placeholder to README. |
| Paper build BAT | `run_dhiman_kadiri_quesada_herrera_build.bat`, an honest scaffold-only verifier until activation. |
| Synchronization BAT and `Tools/push_to_github.ps1` | **Use node 63's exact self-contained `push_to_github.bat` as explicitly requested.** No node-77 PowerShell synchronization helper is needed because 63's BAT implements the workflow itself. SHA-256 is checked by the scaffold verifier. Never executed during setup. |
| `Sources/README.md`, PINS, SHA256SUMS | All present, exhaustive artifact pins and exact provenance. |
| Primary PDF/tar/TeX/processing JSON | Replaced by this paper's v1 PDF/archive and all seven original extracted files, including `.bbl`, two EPS figures and both ancillary scripts. |
| Node-77 GS papers and Iwaniec–Kowalski reference | GS zero-forcing references are not this paper's required sources and are not copied. Relevant Iwaniec–Kowalski excerpt reused byte-for-byte; DKQH's direct Arias/Patel–Yang/Simonič/Kadiri/Patel-thesis references added. |
| `Dependencies/README.md` | Present with compatible root graph, existing proof reuse and import-closure requirements. No fabricated installed dependency. |
| `Extension/README.md` | Present, explicitly reserves future package. |
| Extension root, 44 mathematical Lean modules, Audit, SemanticRegression, lakefile/manifest/toolchain | Inventoried but **deferred**, because conversion is not authorized. No declarations, imports, Lake package or proof stubs created. Proposed equivalents are specified in Checklist/Goal Prompt. |
| `Tools/README.md`, `scaffold.json`, `upstream_snapshot.json` | Present, with planning mode, current metadata and exhaustive file classification. |
| `verify_sources.ps1`, `test_source_verifier.ps1` | Reused verbatim from node 77; source-hash verifier rejects missing, changed, extra, duplicate, escaping, empty and malformed pin entries. Eight tooling fixtures retained under local logs when run. |
| Paper PowerShell runner | Adapted for scaffold-only validation, logs and checked exits. Python standard-library validator covers inventories, statuses, pins and links. No Lean proof commands hidden in setup. |
| `logs/` and `Extension/.lake/` | Generated role accounted for. New own logs only; no copied PASS receipts or compiled Lean artifacts. The uncreated Extension cache is reserved by ignore rules. |

Added because this paper requires them: Computation Review, author-code replay tool/evidence, source-label index, full template path inventory, and selected exact local Lean interface inventory. These are research/verification aids, not a started Lean implementation. No recovery record was created or required.

## Active adaptation

The isolated Lean package now exists with the unchanged root pins and path dependency. Production modules, semantic regressions and exhaustive axiom/linter audit replace the reserved package role. The runner now performs full active-development verification, while maintaining source pins, file classification and owner BAT identity. `Tools/scaffold.json` is the authoritative current file/module inventory. DKQH-03/04/05 are complete; seventeen whole-paper gates remain OPEN. The setup inventory and original source bytes are retained as historical evidence.

The current AFE1 development contains 87 retained files, twenty-one production modules and two verification modules. All are covered by the exact inventory and root import checks; the historical setup inventory above remains a dated record. The public N=0 and general-N general-endpoint and half-integer consumers are mandatory regressions. No additional gate has been closed.

Current reflection/Lemma-7 development: 89 retained files, twenty-three production modules and two verification modules. Both new modules are classified and root-imported; 6/20 gates remain accepted.

Current Lemma-6 development: 95 retained files, twenty-nine production modules and two verification modules. GammaHorizontal, GammaAnchors, GammaStrip, ChiConstants and ChiBound are classified and root-imported; 7/20 gates are accepted after sequential verification.

Current post-DKQH-06 development: 110 retained files, forty-three production and two verification modules. FirstDerivativeTest, WeightedIntegralSums, WeightedIntegrals, WeightedIntegralPhase, LowerIntegralEstimate, MonotoneAmplitude and UpperIntegralEstimate are classified and root-imported. DKQH-06 is DONE; 8/20 accepted gates.

WeightedIntegralPhase discharges the actual power/logarithmic-phase quotient monotonicity for both height signs, applies Lemma 4 on positive truncated intervals, and passes to zero by proved continuity of the integrable primitive. Its source-scale consumer bounds the literal integral of u^(2−s) exp(2πimu) by x^(2−σ)/(π(y−m)), deriving the cutoff condition from 2πxy=|t|. The complete first Lemma-5 sum is now proved in LowerIntegralEstimate and consumed literally by lemma_five_lower_sum_source. The complete upper-tail bound and convergence are now proved in UpperIntegralEstimate and checked by lemma_five_upper_sum_source.

The minimal node-63 Fresnel adaptation now proves the actual symmetric quadratic-integral limit, its principal branch exp(−πi/4), and the quantitative finite-window error. StationaryPoints derives the unique point in the actual decreasing derivative range, proves the shifted phase derivative vanishes, identifies the logarithmic J-phase critical point and its height-sign restriction, and consumes the Fresnel limit to obtain exp(2πi(f(xν)−νxν−1/8))/sqrt(|f″(xν)|). Three independent source consumers check point selection, the finite-window estimate and the phase/amplitude limit. These complete DKQH-06 after the exact-source checks, exhaustive audit and sequential foundation/paper verification. DKQH-11 still requires the nonlinear replacement estimate and all printed B-process error constants. Attribution and exact source hashes are in Dependencies and local_reuse_inventory.json.
