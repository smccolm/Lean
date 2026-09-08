# Tao 2026 Reproduction Manifest

## Manifest status

This is a development manifest, version `erdos-selfridge-source-pin-0.13`. It
reproduces the source identities, pinned build environment, initial source
definitions, frozen Gafni--Tao theorem closure, and Tao's Proposition
2.3(i),(iii). It is not a main-theorem release manifest.

## Pinned source

- Paper: Terence Tao, *Products of consecutive integers with unusual anatomy*.
- arXiv identifier: `2603.27990v2`.
- PDF and TeX archive hashes: `Sources/SHA256SUMS.txt`.
- Provenance and download URLs: `Sources/PINS.md`.
- Baker--Harman--Pintz 2001 PDF: pinned by SHA-256 with DOI, mirror origin,
  and theorem/page locators; this is source provenance, not a formal proof.
- Erdős--Selfridge 1975 PDF: pinned by SHA-256 with archival origin and exact
  theorem locator; this is source provenance, not yet a formal proof.

## Lean package

- Package directory: `Extension/`.
- Package/library name: `Tao2026`.
- Lean toolchain: `leanprover/lean4:v4.30.0`.
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Production modules: `Anatomy`, `Intervals`, `Asymptotics`, `Counting`,
  `FactorialAsymptotics`, `FactorialIntervals`, `FactorialOneTerm`,
  `PrimeIntervals`, `PowerfulNumbers`, `SmoothNumbers`,
  `PublicStatements`, and `Audit`.
- Frozen theorem dependency: the exact 1,226-module import closure of
  `GafniTao.Theorem11`, with 852 `GafniTao`, 291 `RiemannZeta`, and 83
  `PrimeNumberTheoremAnd` source modules.
- Proved content: Proposition 2.3(i) from Mathlib's Bertrand theorem;
  definition-interface lemmas; the uniform discrepancy result
  `exists_uniform_dyadic_exceptional_power_guthMaynard`; exact control of the
  higher-prime-power tail; and
  `exists_dyadic_primeFree_power_guthMaynard`, which gives a nonnegative
  exponent strictly below one for the genuine variable-length dyadic
  prime-free endpoint measure; the finite dyadic assembly; the monotonicity
  treatment of `theta >= 1`; and `taoProposition23iii_guthMaynard`, which has
  the full source range and quantified `O(X^(1-c+o(1)))` conclusion. Exact
  proposition-valued conclusion contracts for Theorems 1.7--1.10 compile,
  but none is proved. The exact inclusive smoothness bridge, unique `p²m`
  representation of `B¹`, and finite identity
  `badOneTermCount_eq_sum_psiNat` are also proved and audited; Proposition
  2.1's analytic estimates and Lemma 1.6 remain open. The positive powerful-
  number `a²b³` parameterization with squarefree `b`, including uniqueness,
  is proved and audited as elementary infrastructure for Corollary 2.11. It
  also yields the exact finite squarefree-cube sum for `VB¹`; the zeta-constant
  asymptotic remains open. All interval predicates now carry the source's
  `H≥1` convention, and the exact type-`F₃`/factorial-square endpoint
  correspondence is proved and audited. On finite ranges, largest-index
  projection is proved to have image exactly `F₃∩[1,x]`, giving the audited
  inequality `factorialThreeCount x ≤ factorialSquareTripleCount x`. The
  one-term set is characterized by square multiples of `s(a!)`; the square
  subfamily gives audited `⌊√x⌋-1` lower bounds for endpoints and triples and
  the full reverse-big-O half of their `x^(1/2+o(1))` scale contracts.

## Reproduction command

From this node directory:

```powershell
cmd /c run_tao_build.bat --no-pause
```

The command verifies:

1. required project files;
2. all three pinned source artifact hashes (Tao PDF, Tao TeX archive, and the
   Baker--Harman--Pintz PDF);
3. all 1,226 frozen dependency hashes and the exact frozen source file set;
4. the raw-only Mermaid architecture contract;
5. the exact Lean, Mathlib, and imported package pins;
6. direct production-root import coverage and forbidden-shortcut absence in
   production and frozen source; and
7. the warning-free `Tao2026` build and executable axiom audit.

The runner emits no persistent log. Console success is evidence only for the
checkout on which it was run.

## Not yet reproducible

The source crosswalk records the initial definitions, main targets, and proved
Proposition 2.3(i),(iii). There is no proved public endpoint for Theorems
1.7--1.10 and no main-theorem proof release to reproduce. The present
axiom audit covers every current Tao production theorem but is not a substitute
for the eventual public-endpoint release audit.
