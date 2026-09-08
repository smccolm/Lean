# Tao 2026 Research Agenda

## Status and scope

This agenda governs the active formalization of Terence Tao, *Products of
consecutive integers with unusual anatomy*, arXiv `2603.27990v2`. The release
scope is now fixed by `Tao Goal Prompt.md` at Theorems 1.7--1.10; none is yet
claimed proved.

The paper studies bad and very bad intervals of consecutive integers, type
`F_3` intervals, and consequences related to the factorial equation
`a_1! a_2! a_3! = m^2`. Those abstract-level descriptions are orientation,
not Lean specifications.

## Phase 0 - repository groundwork

Complete:

- pin the paper and source archive;
- establish project-control document roles;
- reserve isolated source, dependency, package, and tool locations;
- provide a declaration-free Lake shell and honest scaffold check.

## Phase 1 - source reconstruction (active)

Read the v2 TeX in proof order. Produce an exact ledger of:

- definitions and counting conventions;
- theorem and lemma statements;
- parameter ranges and asymptotic uniformity;
- exceptional-set estimates and quantitative thresholds;
- imported results, with the form actually consumed;
- reductions connecting interval anatomy to factorial equations.

The output of this phase belongs in `Tao Crosswalk.md`; do not create a second
competing status document.

## Phase 2 - dependency design

The RH Map gives node 73 incoming arrows from nodes 71 and 74. Treat those as
hypotheses to investigate. Determine the exact theorem-level interface before
copying or importing anything.

Preferred properties of the eventual boundary:

- immutable commit/tag and source hashes;
- minimal public declarations rather than a mutable sibling checkout;
- no reverse import into the frozen releases;
- explicit attribution and license provenance;
- Windows-safe package paths, following node 74 where necessary.

## Phase 3 - statement freeze

The release scope is Theorems 1.7--1.10. Translate each source statement
literally enough that endpoint conventions, multiplicities,
uniformity, exceptional sets, and numerical constants remain visible. Record
every deliberate representation change in the crosswalk before proof work.

## Phase 4 - proof implementation

Build from definitions and reusable lemmas toward the frozen source-facing
contracts. Research probes may be used, but they must remain outside the
production import root. Do not substitute theorem-shaped assumptions for
missing mathematics.

## Phase 5 - release engineering

When real endpoints exist, add:

- a production root;
- `Audit.lean` with permitted-axiom enforcement;
- exact source and dependency closure checks;
- zero-diagnostic builds and forbidden-token scans;
- a truthful reproduction manifest and architecture update.

## Non-goals and non-claims

- copying the full Gafni-Tao implementation;
- changing nodes 71 or 74;
- claiming a result about the Riemann Hypothesis.
