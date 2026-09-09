# Whole-proof operational goal prompt

**Use:** this is the active completion contract for the Tao 2026
formalization. The owner activated it on 8 September 2026. The current verified
stop line is Proposition 2.3(i),(iii), exact one-term sums, the complete
`ζ(3/2)/ζ(3) √x` asymptotic for `VB¹`, the factorial endpoint/counting bridge,
the complete polynomial-coefficient powerful relation from Lemma 3.2, and
the square-family lower-asymptotic milestone. The verified Theorem 2.5
groundwork now also includes its exact contract, reciprocal-phase derivative
formula and elementary size bounds, the exact weighted Vaughan identity, and
the source-scale one-interval/finite-union critical-set measure bounds, plus
the exact bidirectional finite Abel/log-weight reductions for the alternate
Type I form and prime-weight removal, and the low-frequency phase-variation
bounds together with the complex Abel reduction to uniform `Λ-1` discrepancy
bounds, the frozen qualitative PNT bridge giving global `o(k)`, uniform
dyadic-subinterval `o(P)`, and fixed-bounded-frequency `o(P)` phase
comparison, the exact finite Fourier-mode prime-sum/integral assembly and
integer-frequency parameter rescaling, automatic source-interval mode
integrability, and the exact `(2R+1)²` retained-box count and uniform-envelope
bound, plus continuous-weight integrability and the explicit uniform-Fourier-
approximation transfer to the full discrepancy together with exact finite
discarded-mode `ℓ¹` truncation control, summability of the source cubic
`ℤ²` coefficient envelope, vanishing square-box tails, and uniform convergence
of the corresponding finite Fourier polynomials to their series, together
with an exact descent of continuous periodic weights to Mathlib's unit
two-torus and conditional uniform reconstruction of the original weight from
those coefficients, the exact `j=1` absorption,
Type II diagonal split,
transformed-parameter size bounds, and literal product-restricted correlation
rearrangement. The divisor-antidiagonal Vaughan sums are now reindexed exactly
into the same literal product-restricted form, as well as the exact finite quotient-block core of the
shorter-than-dyadic decomposition. Supported coefficient sequences now have
exact pointwise and finite weighted-sum block decompositions with preserved
norm bounds. The product-restricted Vaughan terms now also have exact outer
and double coefficient-block decompositions. The paper's quantitative
polylogarithmic family/count envelopes, the radial and `taoC3Norm` closure of
Fourier coefficient decay from `W` beyond the now-proved one-dimensional
threefold integration-by-parts and two-dimensional Fubini/slice directional
bounds, and the analytic
cancellation estimate remain open.
The Type II correlation kernel is already regrouped exactly by
natural distance with multiplicity at most two. Its one-dimensional
real-power sum is bounded by an exact affine-rpow calculation and has the pure
`N_r F^(-c)` source scale under the explicit endpoint condition for a support
that includes the center. The actual correlation support erases the center;
its zero-distance fiber is proved empty, yielding the pure source scale with
no endpoint hypothesis and propagating it through the complete and actual
short-block squared-inner-sum reductions and the exact Vaughan double blocks.
The all-support audited form still
retains the necessary `1 + O(N_r F^(-c))`. The pointwise source-shaped
kernel-plus-error correlation estimate now feeds through the exact ordered
off-diagonal sum and product-restricted squared-inner-sum reduction, including
specializations to the actual shorter-than-dyadic and Vaughan double blocks.
Their cardinalities are bounded by their chosen block lengths and substituted
into both the conservative and endpoint-free squared-sum estimates.
The high-frequency exponent arithmetic is explicit: a lower bound
`(log P)^d≤F` absorbs `(log P)^b F^(-c)` to `(log P)^(-t)` whenever
`b+t≤dc`.
This includes
the reverse-big-O half of the
`F₃` and factorial-triple square-root scale contracts. The source definitions and public conclusion contracts
compile, the exact
`GafniTao.Theorem11` closure is frozen, and its fixed-power dyadic bridge has
been transferred, with the full prime-power tail and finite prefix assembly,
to Tao's literal global prime-free endpoint measure. Keep going until the exact public theorems and
release gates are complete. Do not mark a mathematical item done because its
definition, interface, conditional version, or surrounding infrastructure
exists.

---

Your goal is to formalize, in Lean, the complete proofs of the four new main
results in Terence Tao, *Products of consecutive integers with unusual
anatomy*, arXiv `2603.27990v2`: Theorems 1.7, 1.8, 1.9, and 1.10. The target is
the literal source mathematics, with its ranges, multiplicities, exceptional
sets, asymptotic quantifiers, and parameter dependencies preserved. This is a
whole-proof goal, not a request for a plausible API, a theorem-statement
collection, or a selected easy fragment.

Work only under
`9. Zero Density, Large Values and Prime Transfer/73 Tao, 2026/`. Keep node 73
as an isolated Lake package and do not import it into the repository-wide
`RiemannZeta.lean`. Treat the released Guth--Maynard and Gafni--Tao packages as
read-only. Do not edit nodes 71 or 74, copy their mutable worktrees wholesale,
or make either older project depend on node 73.

## Frozen source and dependency boundary

Maintain and extend the immutable, machine-checked baseline below. The
Gafni--Tao theorem closure is already frozen; later sources enter only when an
exact crosswalk row requires them:

- Tao source: arXiv `2603.27990v2`, last revised 22 April 2026. The PDF and TeX
  archive are already pinned in `Sources/` and recorded in
  `Sources/SHA256SUMS.txt`.
- Lean: `leanprover/lean4:v4.30.0`.
- Mathlib: commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, matching the
  released node-74 environment unless a later owner-approved migration is
  performed atomically and re-audited.
- Frozen Guth--Maynard boundary: tag `gm-foundation-freeze-v1.0.1`, commit
  `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`.
- Audited PNT+ source revision:
  `4ecb950126c4290293c5662dfe0e884123171df5`. Reuse only the exact
  warning-free closure recorded by node 74 or construct and hash a smaller
  node-73 closure.
- Gafni--Tao: consume an immutable snapshot of the released node-74 package,
  including its reproduction manifest and audit. Record the snapshot commit
  and every copied-source hash in node 73; never import a moving sibling path.
- Candidate related Lean source: `scottdhughes/erdos137`, Apache-2.0, commit
  `3027d9add77a1f2b203977501987c7def955475d`. Review its license, manifest,
  axiom audit, definitions, and every declaration actually reused. Port only
  source-faithful useful lemmas to the node-73 toolchain with provenance. Its
  conditional `abc`/radical-bound finiteness results and any theorem whose
  assumptions are not part of Tao's proof must not enter the dependency graph
  of the four public targets.

The `erdos137` repository is useful evidence for elementary factorization and
interval lemmas, especially `Base.lean`, `Finiteness.lean`, `TaoPoint.lean`,
`RoughPartStructure.lean`, and `SquarefreeCapacity.lean`. It explicitly does
not formalize Tao's analytic density theorem or the complete two-term linear
relation extraction. Treat it as a reviewed partial implementation, not as a
formalization of this paper. Likewise, statement-only formal-conjecture files
containing placeholders are research indexes only and cannot be dependencies,
proof evidence, or copied production code.

Every external theorem must have a row in `Tao Crosswalk.md` giving its exact
source statement, local declaration, immutable provenance, and semantic-gap
status. A matching name, abstract, comment, or numerical experiment is not
proof evidence. A Lean theorem closes a source step only when its full type
matches or a kernel-checked bridge proves the required specialization.

As the crosswalk reaches them, obtain and hash the exact primary sources Tao
uses for Baker--Harman--Pintz prime gaps; Gafni--Tao and Guth--Maynard;
Granville and Hildebrand--Tenenbaum smooth-number estimates; the Matomaki--
Radziwill--Shao--Tao--Teravainen Vinogradov estimate; Montgomery--Vaughan and
Vaughan large-sieve arguments; Aktaş--Murty and the generalized Pell sources;
the three Burgess character-sum papers; Bombieri/Harcos for the
Bombieri--Halasz--Montgomery inequality; and the cited fundamental-lemma sieve
source. Record theorem/page/equation locators, not just bibliography entries.
Prefer author or publisher artifacts and official repositories. Do not
silently substitute a modern statement with different uniformity or constants.

## Exact source objects

Freeze the public statement contracts before building helpers. Formalize at
least the following objects and conventions directly from Sections 1 and 2:

- the interval of consecutive naturals `{N+1, ..., N+H}` with all endpoint and
  positivity conditions visible;
- its product, prime factorization, and largest prime factor, including the
  paper's convention for `1` rather than leaving `max` of an empty prime set
  implicit;
- powerful (squarefull) numbers and the unique square-times-cube
  parameterization needed later;
- the squarefree component `s(n)`, obtained by removing the largest square
  divisor, and its valuation/factorization characterization;
- bad intervals, very bad intervals, and type-`F_3` intervals exactly as in the
  paper;
- `B`, `VB`, and `F_3`, respecting that the first two are unions of all
  elements of qualifying intervals whereas `F_3` records right endpoints;
- the one-term subsets `B^1`, `VB^1`, and `F_3^1`, without silently replacing
  a nontrivial interval by the `H=1` case;
- the smooth-number counting function `Psi(x,y)`, the iterated logarithm, and
  the paper's scales

  `u0 = sqrt(2) * sqrt(log x) / sqrt(log_2 x)`

  and

  `z = exp((1/sqrt(2)) * sqrt(log x) * sqrt(log_2 x))`;
- the factorial equation with strict ordering
  `1 <= a1 < a2 < a3 <= x` and a positive natural square root `m`.

Reuse Mathlib's `Nat.factorization`, prime-factor, squarefree, factorial, finite
product, measure, character, and `Nat.smoothNumbers` infrastructure where the
types agree. If a largest-prime-factor or squarefree-component API is missing,
define it transparently from factorization and prove the complete interface;
do not introduce an opaque oracle.

Never leave `o(1)`, `x^(alpha+o(1))`, `log^(1-o(1)) x`, `~`, or an implied
constant as informal data inside a theorem. Give each a precise filter-based
or epsilon-quantified Lean definition. State which parameters are fixed before
the asymptotic variable tends to infinity, and make uniformity and constant
dependence explicit. Prove equivalences between ergonomic epsilon forms and
the exact public formulations. Lower bounds, upper bounds, equality up to
`x^o(1)`, and asymptotic equivalence are distinct contracts.

## Public release theorems

The public root must expose exact source-facing versions of all four targets:

1. **Theorem 1.7 (bad intervals).** Prove

   `#((B \ B^1) intersect [1,x])
      << #(B^1 intersect [1,x]) / log(x)^(1-o(1))`,

   with the paper's precise asymptotic meaning, and derive
   `#(B intersect [1,x]) = x / z^(2+o(1))` using the one-term asymptotic.

2. **Theorem 1.8 (very bad intervals).** Prove

   `#((VB \ VB^1) intersect [1,x]) << x^(2/5+o(1))`,

   and derive the actual asymptotic
   `#(VB intersect [1,x]) ~ zeta(3/2)/zeta(3) * sqrt(x)`.

3. **Theorem 1.9 (type `F_3`).** Prove

   `#((F_3 \ F_3^1) intersect [1,x]) << x^(1/2+o(1))`,

   and derive `#(F_3 intersect [1,x]) = x^(1/2+o(1))`. Do not strengthen
   this to an asymptotic equivalence with `F_3^1`; that is not what the source
   proves.

4. **Theorem 1.10 (factorial equation).** Prove that the number of triples
   `1 <= a1 < a2 < a3 <= x` for which there exists a natural `m` satisfying
   `a1! * a2! * a3! = m^2` is `x^(1/2+o(1))`, including both the upper and
   lower exponent bounds used by the source.

Use cardinalities of the literal finite sets in these statements. Do not
replace a union by a count of intervals, count representations rather than
values, discard overlaps without a proved multiplicity estimate, or alter
closed/open endpoints because the change is expected to be negligible.

## Source-order proof program

Populate `Tao Crosswalk.md` from the pinned TeX and execute the proof in the
paper's dependency order. At minimum the production graph must close the
following obligations.

### TAO-01: one-term sets and smooth numbers

Formalize Proposition 2.1 in both regimes actually used: the saddle-point
range `y = z^(alpha+o(1))` with `alpha` near `1`, including stability under the
paper's perturbations, and the polylogarithmic range
`y = log(x)^(A+o(1))`, `1 < A` in the stated bounded range. Prove the exact
identity

`#(B^1 intersect [1,x]) = sum_{p <= sqrt(x)} Psi(x/p^2, p)`

with its integrality and endpoint conventions, then Lemma 1.6's asymptotic and
stability estimates. Recursively formalize the required de Bruijn,
Hildebrand--Tenenbaum, or Granville smooth-number results if Mathlib does not
already contain theorem types strong enough for these parameter ranges.

### TAO-02: primes in short intervals and two-variable equidistribution

Formalize Proposition 2.3 in all three forms used by later sections:
Bertrand's postulate, the Baker--Harman--Pintz `0.525` prime-gap consequence,
and the almost-all prime number theorem for every fixed `theta > 2/15` with
the source's exceptional-measure power saving. The intended modern input is
the real node-74 Gafni--Tao theorem, ultimately consuming the frozen
Guth--Maynard zero-density theorem. Begin from
`GafniTao.gafniTaoTheorem11_almostAll_guthMaynard_native` and the literal
exceptional-measure API behind it, or from a stronger audited node-74 public
endpoint whose type matches. Prove the bridge to Tao Proposition 2.3(iii),
including real versus integral endpoints and its `O(x^(1-c+o(1)))` form. A
mere single exceptional set of natural density zero is not by itself the
fixed-power exceptional-measure estimate Tao uses.

Then formalize Theorem 2.5, the Vinogradov two-variable prime
equidistribution estimate for `W(N/p, M/p^j)` with all interval hypotheses and
the `C_3` error. The paper uses the specialization `M=N`, `j=2`, but a reduced
statement is acceptable only after the crosswalk proves that it supplies every
consumer without strengthening a hypothesis.

### TAO-03: uncertainty, large sieve, and algebraic counting

Prove Lemma 2.6 (the Montgomery uncertainty principle), Corollaries 2.8 and
2.9 (pairwise-coprime-modulus large sieve and the simplified form), and every
finite-set/cardinality bridge used later. Existing Hilbert-space facts or
Selberg-sieve files in Mathlib/PNT+ are starting infrastructure, not substitutes
for these source statements.

Prove Lemma 2.10 for the count of square solutions to
`a*n^2 + h = b*m^2`, uniformly over the source's polynomial parameter ranges.
This requires a faithful generalized Pell-equation argument in real quadratic
fields, including degenerate and square-discriminant cases. Then prove
Corollary 2.11 for powerful solutions of `a*n+h=b*m` with the
`x^(2/5+o(1))` bound via the square-times-cube decomposition. Do not postulate
finiteness, cite a computer algebra calculation, or import an unrelated
conditional `abc` theorem.

### TAO-04: very bad intervals

Formalize Lemma 3.1, including
`H <= exp(log(N)^(2/3+o(1)))`, from the prime equidistribution input. Prove
Lemma 3.2's extraction of a nontrivial linear relation `a*n+h=b*m` between
powerful numbers with every size, coprimality, and multiplicity bound. Combine
it with Corollary 2.11, account for all parameter choices and interval
overlaps, and close Theorem 1.8 and its zeta-constant corollary.

### TAO-05: type `F_3` intervals and factorial solutions

Prove Lemmas 4.1--4.3: the `a << H log N` restriction, the same shortness
regime for type-`F_3` intervals, and extraction of the square linear relation
with smooth coefficients. Formalize the paper's case split. Use the large
sieve in the large-`a` regime and the square-solution estimates in the
remaining regimes. Track representations versus right endpoints explicitly.
Close Theorem 1.9, then prove the exact correspondence and multiplicity bounds
needed to close Theorem 1.10 rather than treating the factorial equation as an
informal corollary.

### TAO-06: character sums and sieve inputs for bad intervals

Define the paper's normalized prime character sum `s_Z(chi)` and its
exceptional primitive characters. Prove Lemma 5.1, including both the count of
exceptional characters and the required squared-norm sums. Its prerequisites
must be actual theorems:

- Lemma 5.2, the explicit Burgess estimate for primitive characters with the
  paper's cubefree modulus range `q << H^3.1` and saving `H^(1-0.0163)`;
- Lemma 5.3, the Bombieri--Halasz--Montgomery Hilbert inequality with the exact
  complex inner-product normalization;
- Lemma 5.4, the fundamental-lemma sieve weights
  `lambda_d in {-1,0,1}`, squarefree support `d <= R`, nonnegative divisor sum,
  `lambda_1=1`, and `sum lambda_d/d << 1/log R`.

Mathlib already has substantial Dirichlet-character, conductor, Gauss-sum,
orthogonality, and L-series infrastructure, but the initial audit found no
ready Burgess theorem or source-equivalent fundamental-lemma/large-sieve
package. Recursively formalize the published inputs and their prerequisites.
Do not hide Burgess, a Siegel-zero exception, or the sieve weights behind a
project-level proposition parameter.

### TAO-07: bad intervals and the anti-sieve

Formalize Section 6 in full. This includes Lemma 6.1's admissible ranges;
Lemma 6.2's power-of-two normalization and distinguished anatomy
`p0^2*p1*...*p1000*m'`; the maximal-covering argument; Definitions 6.3 and 6.4
of typicality; and Proposition 6.5's bound for the union of non-typical
intervals. Here the exact node-74 short-interval estimate, smooth-number
estimates, and large sieve must be consumed with all exceptional-set losses
visible.

Prove Proposition 6.6 for the independently sampled prime tuple without
replacing its probability space by an informal random choice. Implement the
anti-sieve split into exceptional `p | l`, the small-prime fiftieth-moment
estimate, and the large-prime mean/variance estimates. Prove Propositions 6.7
and 6.8 through the Dirichlet-character expansion and Lemma 5.1, retaining the
paper's fixed constants (including `1001`, `50`, `0.008`, `0.0163`, and
`3.1`) until a proved monotonicity lemma justifies abstraction. Sum all typical
and atypical contributions, compare them to the one-term set, and close
Theorem 1.7.

## Proposed production modules

Use the source dependency graph, not this list, as the final authority, but
start with a structure no coarser than:

```text
Tao2026/Asymptotics.lean
Tao2026/Anatomy.lean
Tao2026/Intervals.lean
Tao2026/SmoothNumbers.lean
Tao2026/PrimeIntervals.lean
Tao2026/Vinogradov.lean
Tao2026/LargeSieve.lean
Tao2026/QuadraticRelations.lean
Tao2026/PowerfulRelations.lean
Tao2026/VeryBad.lean
Tao2026/FactorialIntervals.lean
Tao2026/DirichletCharacters.lean
Tao2026/Burgess.lean
Tao2026/FundamentalSieve.lean
Tao2026/ExceptionalCharacters.lean
Tao2026/BadIntervals.lean
Tao2026/PublicTheorems.lean
Tao2026/Audit.lean
```

Split modules further when this prevents hidden circularity or keeps source
lemmas auditable. Import every production module from `Tao2026.lean`; no
unimported proof island counts toward completion. Keep experiments and API
probes outside the production root, label them clearly, and subject any probe
promoted into production to the same audits.

## Proof-integrity contract

No production or supporting Lean source may contain `sorry`, `admit`, a
project `axiom` or `constant` used as a mathematical fact, `unsafe` proof
bypasses, `native_decide`, `implemented_by`, hidden oracles, theorem-equivalent
hypotheses, or toy replacements for source objects. This applies equally to
vendored code, generated files, scratch Lean files kept in the node, and
dependencies under node-73 control.

A conditional theorem is allowed only as an honestly named intermediate
milestone when its hypotheses are narrower, reusable published inputs. It is
not a completed source theorem. For release, recursively prove every such
input or consume a pinned, audited Lean theorem, and ensure the four public
endpoints have no extra mathematical hypotheses.

Do not use finite computation to prove an asymptotic analytic result. Exact
rational normalization, ring arithmetic, interval endpoint checks, and finite
enumerations are appropriate only where they really close those finite goals.
Do not infer a theorem from a plot, floating-point optimizer, paper comment,
blog post, or successful test case.

Preserve a zero-warning policy: no Lean warning, linter suggestion, deprecated
declaration use, unused-variable diagnostic, or tactic diagnostic in the
canonical build. Every meaningful source theorem and every public endpoint
must have `#print axioms` coverage showing only the explicitly permitted
Lean/Mathlib logical axioms (`propext`, `Classical.choice`, and `Quot.sound`
when genuinely introduced transitively). Investigate any additional axiom
immediately.

## Required execution discipline

Work in dependency-closing increments, but retain the entire four-theorem goal
as the stopping condition. For each increment:

1. add or update its exact crosswalk row before claiming it;
2. prove the smallest source-faithful declarations that unblock a real
   downstream consumer;
3. run focused builds while iterating;
4. import the result through the production root;
5. run its axiom and forbidden-token checks;
6. update documentation only to the level actually established; and
7. continue to the next unresolved source dependency.

When an expected library theorem is absent, search Mathlib, the frozen GM and
GT interfaces, the audited PNT+ closure, and pinned primary-source repositories
by theorem type and semantics. If still absent, formalize the published proof
and its prerequisites. Do not end the task by converting the missing theorem
into a new assumption, a roadmap item, or an invitation for another agent.

Maintain an explicit ledger for all thresholds and losses: `x`, `N`, `H`,
`theta`, `c`, smoothness parameters, dyadic scales, prime ranges, exceptional
measures, `o(1)` witnesses, logarithm domains, congruence moduli, character
conductors, interval-cover multiplicities, and implied-constant dependence.
Keep strict inequalities strict. Handle small values separately rather than
using asymptotic notation outside its eventual range.

## Release acceptance gates

Continue extending the warning-failing principal verifier while preserving the
owner-facing command:

```powershell
cmd /c run_tao_build.bat --no-pause
```

Completion requires one successful run which, for the current checkout:

1. verifies the Tao PDF and TeX hashes and every vendored/captured dependency
   hash;
2. verifies the exact frozen node-71 and node-74 boundaries;
3. builds the complete isolated dependency closure and `Tao2026` root;
4. fails on every Lean warning, linter suggestion, tactic diagnostic, or
   deprecated API diagnostic;
5. runs `Tao2026/Audit.lean` and checks the transitive axioms of Theorems
   1.7--1.10 plus the source-critical intermediate theorems;
6. scans all node-controlled Lean sources for forbidden shortcuts and checks
   that every production source is reachable from the root;
7. runs semantic regression tests for interval endpoints, one-term/nontrivial
   set distinctions, squarefree-component conventions, multiplicity, and the
   asymptotic interfaces; and
8. writes an unsuppressed reproducibility log whose exact status is recorded
   in `Tao Reproduction Manifest.md`.

Synchronize `README.md`, `Tao Architecture.md`, `Tao Checklist.md`,
`Tao Research Agenda.md`, `Tao Crosswalk.md`, `Tao Sources.md`, and
`Tao Reproduction Manifest.md` only after the matching Lean gates pass. The
architecture must distinguish proved, conditional, dependency-supplied, and
unstarted nodes. Documentation may not call the project complete based on a
focused build or an aspirational diagram.

Do not run `push_to_github.bat` or add any push command to the verifier or CI.
The owner controls commits and publication. Do not describe this work as a
path to the Riemann Hypothesis, and do not claim peer review, publication,
canonicality, independent verification, new mathematics, or complete
formalization until the literal release gates support that statement.

The legitimate stopping condition is a passing release verifier for all four
public theorems. If a requested source statement is false as written,
completion may instead be a kernel-checked counterexample or contradiction
which identifies the exact false statement and supports a source-level
erratum. Difficulty, proof length, missing library convenience, a failed
tactic, or completion of a substantial subset is not such a result and is not
a reason to stop.

---
