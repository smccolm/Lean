# Instructions for AI Contributors

These instructions apply to every file and subdirectory in this repository. They are mandatory for AI agents and automated coding tools contributing to the Riemann Zeta project.

## Mission

Develop the existing Lean 4 project into a reproducible, kernel-checked formalization of the Guth–Maynard zero-density argument and its analytic inputs. Preserve the existing repository as the canonical codebase. Keep the Lean source, audit, README, paper, and research-progress documentation mathematically consistent.

Correctness and honest dependency reporting take priority over apparent progress, theorem count, build speed, or eliminating an error by weakening a statement.

## Absolute Proof-Integrity Rules

1. **Never use `sorry`.** Do not add `sorry`, `by sorry`, `exact sorry`, generated `sorryAx`, or any equivalent placeholder in any Lean file.
2. **Never use `admit`.** Do not use tactics, macros, or generated declarations that reduce to an admitted proof.
3. **Never declare project axioms.** Do not add `axiom`, use `constant` to postulate mathematical data or proofs, or replace a missing proof with an axiom under names such as `unconditional`, `native`, `assumption`, `oracle`, or `helper`.
4. **Never hide the desired result in a definition or hypothesis.** A proposition definition, structure field, typeclass, module-level variable, or theorem parameter must not be equivalent to the result that the theorem claims to derive.
5. **Never replace mathematics with a toy model.** Do not substitute constants such as `0`, `1`, `True`, the empty set, or an uninterpreted function for the intended mathematical object merely to make downstream declarations compile.
6. **Never disguise a specification as a proof.** A compiling `def ... : Prop` is a statement, not a proved theorem. A theorem that returns an assumed proposition is conditional, not unconditional.
7. **Never use unsafe or external evaluation as proof evidence.** Do not use `unsafe`, `native_decide`, `implemented_by`, external solver output, generated object code, or runtime assertions to bypass Lean's kernel.
8. **Never conceal circularity.** Before accepting a new hypothesis, unfold it and verify that it is strictly narrower than the desired conclusion and corresponds to a genuine upstream mathematical input.
9. **Never weaken the intended theorem silently.** Preserve domains, quantifiers, parameter ranges, multiplicities, separation conditions, constants, and asymptotic dependencies. Document and justify every intentional reformulation.
10. **Never claim global success while violations remain.** Existing `sorry`, project axioms, excluded failing modules, or unaudited theorem dependencies must be reported explicitly. Replacing `sorry` with `axiom` is not progress toward proof completion.

These rules apply to scratch, test, generated, and archived Lean files as well as canonical modules. If a Lean file is intentionally non-production and cannot satisfy the rules, remove it from the repository or convert it into non-Lean documentation rather than leaving an admitted declaration.

## Permitted Assumptions in Conditional Theorems

An explicit theorem parameter may represent a genuinely upstream result when the current research milestone is intentionally conditional. Such a parameter is permitted only when all of the following hold:

- it is stated directly in the theorem signature;
- it is individually named and mathematically narrower than the conclusion;
- its exact quantifiers and constant dependencies are visible;
- it matches an identified source theorem or a precisely documented provisional interface;
- the proof performs the advertised downstream deduction rather than returning the parameter unchanged; and
- the README, paper, audit, and progress document identify the result as conditional.

For example, a Goal B transfer theorem may accept separately stated large-values, Type II, local-zero-count, and mean-value hypotheses. It may not accept `GuthMaynardZeroDensity ...` itself or a definitionally equivalent wrapper.

Standard logical axioms inherited from Lean and Mathlib—normally `propext`, `Classical.choice`, and `Quot.sound`—are permitted when they arise from ordinary Mathlib use. They must remain visible in `#print axioms` output and must not be confused with project-specific mathematical assumptions.

## Mathematical Substance Rules

- Definitions must model the actual objects required by the research agenda. In particular, detector coefficients must implement the intended truncated Möbius expression rather than a constant proxy.
- A lemma with conclusion `True` is not an implementation of an analytic, combinatorial, or number-theoretic result.
- A reflexivity proof is acceptable only for a genuinely definitional identity. Documentation must not present it as a nontrivial expansion, estimate, or analytic theorem.
- Positivity of a proposed bound's right-hand side does not prove the bound.
- A general theorem is not proved by checking a single boundary case.
- Zero-counting claims must track the intended rectangle convention and analytic multiplicity. Any provisional construction must be clearly marked and must not support unconditional claims.
- Asymptotic notation must use explicit Lean definitions with all epsilon quantifiers and allowed parameter dependencies represented faithfully.
- Search Mathlib before reproving a result, but verify the exact semantics and audit the resulting theorem dependencies.

## Zero-Warning and Linter Policy

The project owner's proof run must contain no Lean warning or linter diagnostic from project source. A build stage that exits successfully but prints `warning:` is not clean and does not satisfy the project evaluation standard.

This requirement includes, without limitation:

- unused-variable and unused-argument warnings;
- deprecated syntax, tactics, declarations, or APIs;
- tactic and declaration-style warnings emitted by Lean;
- declarations reported as using `sorry`;
- declaration, documentation, and formatting linters; and
- warnings produced while compiling retained tests, scratch files, or explicitly covered production modules.

Fix the cause of each diagnostic. Do not hide it with `set_option linter... false`, blanket linter exclusions, output filtering, log redirection, or a runner rule that ignores warnings. An underscore-prefixed or anonymous binder is acceptable only when the parameter is intentionally irrelevant to the mathematically faithful statement; it must not conceal a malformed interface or unused hypothesis that should be removed.

`run_lake_build.bat` must treat any Lean `warning:` diagnostic from project compilation or audit execution as a failed evaluation gate. Its final `PASS` requires zero Lean errors, zero Lean warnings, a passing dependency audit, and passing proof-integrity scans.

## Required Development Workflow

Before editing:

1. Read `Guth_Maynard_Formalization_Research_Agenda.docx`, `Research Agenda Progress.MD`, `Lean Alignment Fix Agenda.md`, `Proof Architecture.md`, `README.md`, `Paper_Riemann_Zeta.md`, `RiemannZeta/Audit.lean`, `lakefile.toml`, and `lean-toolchain` as relevant to the task.
2. Inspect the current working tree and preserve all user changes. Do not overwrite or revert unrelated work.
3. Identify whether the target is a definition, a formal statement, a conditional theorem, or an unconditional theorem. State that status accurately.
4. Inspect the exact source theorem and existing Mathlib APIs before designing the Lean signature.

During implementation:

1. Work in small, kernel-checked increments.
2. Keep the intended theorem statement fixed unless a mathematical correction is documented.
3. Prefer small supporting lemmas with substantive conclusions over monolithic proof blocks.
4. Compile the edited module after each meaningful change.
5. Do not make unrelated cleanup changes in files owned by the user.

## Persistence and Legitimate Stopping Conditions

A request to **prove**, **fix**, **complete**, **fully implement**, or **do** a Shitlist item binds the agent to the requested end theorem and its stated acceptance test. Supporting lemmas and successful checks are implementation milestones, not substitutes for that deliverable.

1. **Do not stop at an intermediate lemma.** A new definition, derivative formula, finite reduction, conditional theorem, focused build, or audit-clean helper is not a stopping condition while the requested theorem remains unproved.
2. **Do not convert unfinished implementation into a planning handoff.** Isolating the next subproblem, writing a list of remaining steps, or updating the documentation does not satisfy a request to perform those steps.
3. **If a safe in-scope next step exists, take it.** Continue from one lemma to the next, including through difficult analytic, combinatorial, and integration work. Difficulty, proof length, slow elaboration, failed first approaches, and the need for additional research are expected parts of the task rather than reasons to end the turn.
4. **Treat verification as a gate, not an exit ramp.** Passing a focused build or axiom audit authorizes continuation to the next obligation. Run final verification only after the requested mathematical output exists, while still using incremental checks during development.
5. **Documentation must follow proof status, not replace proof work.** Synchronize the Shitlist, progress report, and proof architecture when status changes, but then continue implementing if the user's requested acceptance condition is still open.
6. **Do not manufacture a blocker.** “This is substantial,” “this requires many lemmas,” “no existing repository proves it,” “the remaining step is now precisely isolated,” or “this would take another iteration” are not blockers.
7. **A legitimate stop before completion requires an actual impasse:**
   - a necessary action requires new user authority or an external credential;
   - a required external service, dependency, or tool is unavailable after reasonable alternatives and retries;
   - the requested statement is false or inconsistent, with a concrete mathematical demonstration; or
   - every identified proof route has reached a specific technical obstruction that cannot be resolved with the available code, Mathlib APIs, source literature, or a faithful reformulation.
8. **Before reporting an impasse, exhaust the available work.** Inspect relevant local and external sources, try materially different proof decompositions, prove all independent supporting obligations, preserve compiling code, and state the exact failed Lean goal or mathematical contradiction. A first failed tactic or cumbersome formalization is not exhaustion.
9. **Never describe partial progress as completion.** If a legitimate impasse remains, say explicitly that the requested item is incomplete, identify the exact acceptance clause still failing, and distinguish proved infrastructure from the missing end theorem.
10. **Explicit persistence language has force.** When the user says “fully,” “completely,” “do it,” “do not stop,” or objects to previous stopping, continue until the requested acceptance test passes or one of the legitimate impasses above is established. Do not end merely to provide a progress report.

The operational test is simple: before ending an implementation turn, ask whether the user could truthfully cross out the requested Shitlist item under its existing completion test. If not, and a safe in-scope proof step remains, continue working.

Before declaring completion:

1. Scan the entire repository for prohibited placeholders and postulates.
2. Build every intended production module, not merely the modules reachable from the current default target.
3. Run explicit axiom audits for every new or changed public theorem and every agenda-critical downstream theorem.
4. Verify that no new theorem depends on `sorryAx` or a project-specific axiom.
5. Confirm that the default root module imports every intended production module. A successful default build is insufficient if substantive files are outside the import graph.
6. Confirm that focused builds and the principal runner emit no Lean warning or linter diagnostic from project source.
7. Update the README, paper, audit file, Shitlist, research-progress document, and canonical proof-architecture diagram when proof status or dependencies change.
8. Report exact commands, results, remaining assumptions, warnings, and failures. Do not summarize a warning-producing or partial build as “clean.”

## Principal Human-Facing Evaluation: `run_lake_build.bat`

`run_lake_build.bat` is a first-class project interface and the principal human-facing evaluation of the formalization. The project owner will use this file to run and inspect the overall proof. AI agents must treat its correctness, clarity, and continued operation as part of the proof deliverable, not as incidental build tooling.

Lean does not execute a proof like an ordinary program; it validates the proof by elaborating declarations, compiling the relevant modules, and checking dependencies in the kernel. `run_lake_build.bat` must make that verification process visible and understandable to a human who launches the file directly.

The runner's intent is to provide one action that:

- starts from the repository root regardless of the caller's current directory;
- uses the toolchain pinned by `lean-toolchain`;
- builds the default Lean project;
- explicitly builds intended production modules that are not yet reachable from the root import graph;
- executes the project's Lean axiom audit;
- scans the entire Lean source tree for forbidden proof shortcuts;
- reports each stage as pass or fail without suppressing warnings or errors;
- treats any Lean warning from project source as a failed evaluation gate;
- writes a complete timestamped log under `logs/`;
- returns exit code `0` only when every required build, audit, and integrity gate passes; and
- pauses for a human when launched by double-click while supporting `--no-pause` for agents and CI.

Rules for maintaining the runner:

1. Do not delete, rename, bypass, or materially narrow `run_lake_build.bat` without the project owner's explicit permission.
2. Keep its production-module target list synchronized with the actual project. Adding a production module requires adding it to the root import graph or to the runner's explicit coverage until the root graph is repaired.
3. Keep its integrity scans synchronized with `AGENTS.md` and its audit stage synchronized with `RiemannZeta/Audit.lean`.
4. Never make the runner return success by excluding a failing module, ignoring a nonzero exit code, filtering an error from the log, weakening a scan, or relabeling a failed stage.
5. A successful default `lake build` alone must not be presented as an overall pass when the runner reports failure.
6. A runner `PASS` is valid only when the audit is a genuine dependency audit and all intended production modules are included.
7. A runner `PASS` is invalid if any project build or audit stage emits a Lean warning, even when that stage's process exit code is `0`.
8. Do not suppress, filter, downgrade, or globally disable warnings to obtain a pass. Repair the source of each diagnostic.
9. After changing Lean source, imports, `lakefile.toml`, `lean-toolchain`, the audit, or the runner itself, execute:

   ```powershell
   cmd /c run_lake_build.bat --no-pause
   ```

10. Report the runner's final exit code, final status, log path, every remaining failed stage, and every remaining warning in the handoff.
11. If the runner itself is broken or cannot be executed, the task is not fully verified. Repair it or report the exact environmental blocker; do not substitute an unaudited success claim.

The current repository is expected to produce `FAIL` until the named research-output defects are repaired. The build, warning, dependency, and integrity gates currently pass; the output gate fails. That failure is useful evidence. Agents must preserve its honesty while progressively converting each missing theorem into a genuine pass.

## Mandatory End-of-Turn Commit-Message Update: `push_to_github.bat`

`push_to_github.bat` is the project owner's repository-synchronization interface. The project owner runs this script; AI agents must not run it unless separately and explicitly instructed to do so.

On every turn in which an agent creates, edits, renames, or deletes any repository file, the agent must update the commit message in the script's `git commit -m "..."` command so that it accurately summarizes that turn's repository changes.

This requirement is permanent and has the following operational meaning:

1. Complete all implementation, documentation synchronization, builds, audits, integrity scans, status inspection, and other repository work first.
2. Make the commit-message edit in `push_to_github.bat` the final repository-file edit and final tool action of the turn.
3. After updating that message, do not mutate or inspect files, run builds or audits, execute Git commands, or invoke another tool before the final user-facing response.
4. A turn that makes no repository-file change does not require a commit-message update.
5. Write a concise, specific message describing the substantive changes made during the turn; do not leave a stale or generic message.
6. Do not execute `push_to_github.bat` as part of this rule. The project owner will review and run it.

## Mandatory Checks

Use repository-wide searches equivalent to the following before handoff:

```powershell
rg -n "\b(sorry|admit)\b|sorryAx" -g "*.lean" .
rg -n "^\s*(axiom|constant)\b" -g "*.lean" .
rg -n "\b(native_decide|implemented_by|unsafe)\b" -g "*.lean" .
```

Review matches in comments as well as code so stale documentation is corrected. The final code scan must contain no prohibited declaration or proof term.

The focused module build and principal runner log must also contain no line beginning with `warning:` for project source. A zero exit code does not override this diagnostic requirement.

Run the principal overall evaluation using the pinned toolchain:

```powershell
cmd /c run_lake_build.bat --no-pause
```

For focused development, also run the relevant direct project build:

```powershell
lake build
```

Also build any production module not reachable from the root import graph. The long-term repository invariant is that all production modules are imported and checked by the default target.

For each public theorem, add or run an explicit audit such as:

```lean
#print axioms RiemannZeta.GuthMaynard.exampleTheorem
```

Acceptable output may include standard Lean/Mathlib logical axioms. It must not include `sorryAx`, a project-declared axiom, or an assumption equivalent to the audited theorem.

## Audit File Requirements

`RiemannZeta/Audit.lean` must be an actual dependency audit, not a categorization by declaration name or declaration kind.

- Maintain an explicit list of all public and agenda-critical theorems.
- Run `#print axioms` or an equivalent environment-level dependency inspection for each listed theorem.
- Import every production module.
- Fail visibly when a theorem depends on `sorryAx` or a project-specific axiom.
- Do not classify a declaration as proved merely because Lean records it as a theorem.
- Keep the audited declaration count synchronized with the actual list.

## Documentation and Claim Control

Use the following status vocabulary consistently:

- **Defined/stated:** Lean accepts the definition or proposition, but no proof is claimed.
- **Conditionally proved:** Lean proves an implication from explicit, narrower hypotheses.
- **Kernel-checked:** The theorem has no `sorryAx` or project-specific axiom dependencies and all containing production modules compile.
- **Project theorem complete:** The exact intended statement is kernel-checked, all required modules are in the default build, its dependency audit is clean, and the documentation is synchronized.

Do not use “unconditional,” “fully formalized,” “complete,” “clean build,” “zero axioms,” or “zero `sorry`s” unless the repository-wide checks establish the claim literally.

Every substantive iteration must leave:

- compiling Lean code for the claimed scope;
- an explicit axiom audit;
- accurate proof-status documentation;
- a precise account of remaining obligations; and
- no new hidden assumptions or placeholder mathematics; and
- zero Lean warnings in the files changed and in every claimed-clean evaluation scope.

## Mandatory Proof-Architecture Synchronization

`Proof Architecture.md` is the canonical Mermaid view of the logical proof dependencies and completion status. `Lean Alignment Fix Agenda.md` remains the authority for Shitlist task numbers and acceptance tests, while `Research Agenda Progress.MD` remains the evidence-based status report.

Whenever a change alters a theorem's proof status, an open obligation, a dependency edge, or a Shitlist assignment, update all three documents in the same change. Every unfinished Mermaid node must name its owning Shitlist number. A crossed-out Shitlist item must have no unfinished node in the diagram, and a newly discovered obligation must be assigned to an existing open item unless the project owner explicitly changes the exhaustive completion contract. Before handoff, verify that the diagram, Shitlist, and progress report make identical claims about what is done and what remains.

## Handling the Current Incomplete Baseline

The repository currently has no project axiom, `sorryAx` dependency, admitted proof, excluded Lean file, or warning-producing declaration in the principal evaluation scope. It remains mathematically incomplete because the named #15, #18, and #19 output theorems are absent and the principal runner therefore returns `FAIL`. Preserve the clean integrity baseline while completing those outputs.

While research outputs remain incomplete, the agent must:

- introduce no new violation;
- reduce or preserve, never increase, the set of existing violations;
- state exactly which violations remain;
- avoid describing the repository as globally compliant; and
- refuse any shortcut that merely renames, wraps, or relocates an unproved assumption.

If a requested theorem reaches a legitimate impasse under the persistence rules above, preserve only faithful statements and theorems with legitimate explicit upstream parameters. Record the precise missing lemma and leave the code kernel-checkable. This is a fallback after exhaustive work, not permission to stop when an implementable next step remains. An honest, narrow obstruction is a valid research result; an admitted theorem is not.
