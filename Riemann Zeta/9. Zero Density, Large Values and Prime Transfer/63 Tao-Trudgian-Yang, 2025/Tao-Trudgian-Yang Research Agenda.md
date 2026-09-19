# Tao--Trudgian--Yang 2025 research agenda

## Executive assessment

This project is feasible as a staged extension of two unusually strong local
assets:

- ANTEDB's newer Lean foundation already models the paper's cheap asymptotic
  language and exponential-sum growth function; and
- the neighboring Guth--Maynard project already proves the deepest large-value
  and zero-density input used by the 2025 paper.

The main difficulty is not rational arithmetic. It is building faithful
interfaces between four semantic layers: asymptotic exponential sums,
large-value patterns, zeta zero counts, and additive energy. The optimization
should be formalized as proof-producing exact finite certificates only after
those meanings are fixed.

## Implementation status (19 September 2026)

EPZAE-00--05, EPZAE-07--08, EPZAE-16--17, EPZAE-20, EPZAE-22--23,
EPZAE-25, and EPZAE-31 pass. The project now has one Lean 4.30 graph,
an attributed frozen ANTEDB subset, exact rational/piecewise/polyhedral
certificate kernels, and the paper's analytic exponent-pair definition with a
proved non-asymptotic equivalence, an exact multiplicity-weighted zero-
rectangle bridge, the extended-real density exponent with its epsilon-loss
interface, and exact shifted-convention bridges for the native Ingham,
Huxley, and Guth--Maynard estimates, faithful general/zeta large-value
patterns and least-exponent interfaces, and the exact `guth-maynard-lvt`
bound obtained from the native publication theorem through proved support,
reflection, phase, norm, threshold, and epsilon-loss conversions, together
with unit-tolerance indexed-
multiset energy and its quadratic/cubic bounds. These bounds now induce the
extended-real general and zeta exponent comparisons `2LV ≤ LV* ≤ 3LV`, even
at infinite infima. The non-asymptotic energy regions also imply the necessary
`ρ ≤ τ` and `2ρ ≤ ρ* ≤ 3ρ` constraints. The
remaining checklist items are open; none of the advertised
paper outputs is complete.

## Phase 0: freeze and compatibility

**Complete.** The selected ANTEDB subset was backported to the local Lean 4.30
graph with two documented compatibility edits, and the two-source import spike
is part of the default build and audit.

1. Preserve arXiv v1 PDF and TeX source with hashes.
2. Preserve the paper-time ANTEDB snapshot and the current Lean-enabled
   snapshot as separate archives.
3. Compare Lean `v4.30.0` (local Guth--Maynard) with ANTEDB `v4.32.0`.
4. Choose one route and document it:
   - port the selected ANTEDB modules back to the local `v4.30.0` graph;
   - upgrade the Guth--Maynard dependency graph to `v4.32.0`; or
   - upstream the new work directly in ANTEDB and build a separately pinned
     bridge to the local foundation.
5. Prove a two-module import spike before creating the full package.

Recommended route: first test a narrow backport of ANTEDB's `Basic` and
`ExponentialSums` modules to the local `v4.30.0` mathlib revision. Their source
surface is small enough to evaluate, while upgrading the completed
Guth--Maynard tree is high risk.

## Phase 1: exact certificate kernel

**Core acceptance test complete (EPZAE-03--05).** Exact denominator signs for
all displayed output formulas, generic envelope/polyhedral soundness, and the
optimized Bourgain endpoint/coverage certificates are kernel-checked. The
deterministic generator remains separate work under EPZAE-06.

Build reusable, domain-independent machinery for:

- normalized rational functions with denominator-positivity side conditions;
- affine bounds over closed/open rational intervals;
- exact crossover computation;
- maxima and minima of finite families;
- convex combinations and convex-hull witnesses;
- rational polyhedra represented by finite inequalities;
- projection certificates carrying explicit eliminated-variable witnesses;
- piecewise envelope coverage and endpoint agreement.

The certificate format must be deterministic and small enough to audit. A
Python script may emit rational witnesses, but Lean must check every equation,
inequality, interval cover, and sign condition.

First milestone: certify a harmless subset of the beta table and prove that a
specified affine line dominates on its stated interval.

## Phase 2: exponent pairs and beta

**In progress.** EPZAE-07--08 are complete. Convexity and beta duality are the
next open analytic edge.

1. Reuse ANTEDB's `exponentSumGrowthExponent` and non-asymptotic equivalence.
2. define the analytic `ExponentPair` predicate;
3. prove monotonicity and convexity;
4. prove beta/exponent-pair duality, including endpoint and reflection handling;
5. formalize or import exact versions of A, B, C, and Sargos D;
6. formalize Heath--Brown's kth-derivative beta bound;
7. certify every beta-table segment needed by the four output pairs; and
8. prove the four `new-exp-pair` conclusions from global affine bounds.

The D-process sentence in the paper says it “in practice” yields an exponent
pair. Lean must contain the actual duality argument; it may not record D as an
unproved constructor.

## Phase 3: large-value semantics

**In progress.** EPZAE-16--17 and EPZAE-20 are complete. In particular,
`guthMaynard_largeValueBound` proves the source maximum of all three affine
exponents from the native publication theorem. Elementary/classical and
zeta-specific large-value inputs remain under EPZAE-18--19 and EPZAE-21.

1. Define large-value patterns with exact interval, separation, coefficient,
   phase-sign, and normalization conventions.
2. Define `LV(sigma,tau)` and `LV_zeta(sigma,tau)` with explicit epsilon-loss
   quantifiers rather than an informal least exponent if that gives a cleaner
   public API.
3. Prove equivalence with the paper's least-exponent formulation.
4. Formalize subdivision, lower bounds, L2 mean value, raising to a power, and
   zeta-specific bounds.
5. Bridge the completed local Guth--Maynard theorem to equation
   `guth-maynard-lvt` with all coefficient and interval conversions visible.
6. Formalize only the portions of Bourgain/Jutila/Huxley/Heath--Brown needed by
   the target certificates, then broaden after the endpoints compile.

## Phase 4: zero density

1. Define the paper's multiplicity-weighted `N(sigma,T)`.
2. Prove its equality/inequality bridge to the local `zeroCountRect` convention.
3. Define the density exponent `A(sigma)` and its epsilon-loss API.
4. Formalize the Type I/Type II zero-density-from-large-values theorem and the
   corollaries used by the paper.
5. Reuse local Ingham, Huxley, and Guth--Maynard results only through exact
   bridges.
6. Prove `hb-density2`.
7. Prove `bourgain-density-improved` and both subrange simplifications.
8. Formalize Bourgain's exponent-pair density theorem and its side conditions.
9. Certify the eight-piece optimized bound, including all crossover points and
   admissibility conditions.
10. Treat the full best-known table as a corollary/validation artifact, not as
    the definition of `A`.

## Phase 5: additive energy

1. Define finite multisets of ordinates and approximate additive energy with
   the source tolerance and multiplicity.
2. Prove the elementary energy inequalities and stability under bounded
   perturbation used in the zero-to-large-value transfer.
3. Define `LV*`, `LV*_zeta`, `A*`, `E`, and `E_zeta` faithfully.
4. Prove the non-asymptotic energy-region equivalence.
5. Prove the zero-density-energy transfer and the source's weakened powering
   lemma, preserving the fact that the cardinality, energy, and double-zeta
   witnesses may be different subsequences.
6. Formalize Heath--Brown's five-variable max inequality.
7. Turn every polyhedral projection used by `Add-est` into an exact certificate.
8. Prove all nine clauses and their interval endpoints.

The additive-energy section has the highest semantic risk because informal
subsequence selection can silently identify witnesses that the paper
explicitly warns may differ.

## Phase 6: release integration

1. Assemble `PublicTheorems.lean` with source-facing names and statements.
2. Add endpoint, crossover, and convention checks to
   `SemanticRegression.lean`.
3. Import all production modules from the root module.
4. Maintain an exhaustive theorem/axiom audit.
5. Add the warning-failing build runner, source-hash checks, snapshot checks,
   deterministic certificate regeneration check, and Python reproduction test.
6. Synchronize every planning/control document.

## Risk register

| Risk | Why it matters | Mitigation |
|---|---|---|
| Lean 4.30/4.32 split | Local and upstream foundations cannot share incompatible oleans | Resolve EPZAE-01 before architecture hardens |
| Cheap-asymptotic semantics | Sequence/subsequence arguments hide uniformity and choice | Reuse ANTEDB's proved API and expose every subsequence |
| Zero convention mismatch | Paper uses `|Im rho| <= T`; local work uses rectangles/slabs | Dedicated proved `ZeroCountBridge` plus regressions |
| Phase and coefficient conventions | `n^{it}` vs `n^{-it}`, support-only vs ambient coefficient bounds | Explicit conjugation and extension-by-zero lemmas |
| Optimization trusted accidentally | Python/SciPy output is not a theorem | Rational witnesses checked in Lean |
| Denominator signs | Rational bounds can reverse under multiplication | Carry interval-specific positivity lemmas in certificates |
| Open/closed endpoints | Several tables mix `<` and `<=` | Formal interval cover with overlap equality proofs |
| Additive-energy multiplicity | Set simplification changes the theorem | Use multisets or indexed families from the start |
| Different powering witnesses | Source lemma permits three different output tuples | Do not package them as one stronger witness |
| Source editorial slips | TeX contains minor variable/label inconsistencies | Maintain an errata ledger in the crosswalk |
| Over-formalizing literature | Full books/papers would swamp the target | Formalize the exact consumed theorem surfaces first |

## Next sprint

1. Prove exponent-pair convex closure directly from the analytic estimate.
2. Prove the easy direction “exponent pair implies affine beta bound.”
3. Prove the converse, including the `alpha = 0,1` endpoints and beta
   reflection bookkeeping.
4. Extend the installed deterministic extractor and byte-for-byte runner diff
   gate to every certificate table.
5. Begin exact A/B/C process theorem surfaces only after duality compiles.

Triangle membership and affine arithmetic remain prerequisites, not claims
that any of the four advertised points is already an exponent pair.
