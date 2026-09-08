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

## Phase 0 - repository groundwork (complete)

Complete:

- pin the paper and source archive;
- establish project-control document roles;
- reserve isolated source, dependency, package, and tool locations;
- provide an isolated Lake package and honest development check.

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

## Phase 2 - dependency design (first boundary complete)

The first required analytic boundary is now fixed at the recursive import
closure of `GafniTao.Theorem11`. Node 73 contains an immutable, per-file-hashed
copy of its 1,226 reachable Lean modules and imports that package rather than a
mutable sibling checkout. Further dependencies remain crosswalk-driven.

Properties enforced for this boundary and required of later ones:

- immutable commit/tag and source hashes;
- minimal public declarations rather than a mutable sibling checkout;
- no reverse import into the frozen releases;
- explicit attribution and license provenance;
- Windows-safe package paths, following node 74 where necessary.

## Phase 3 - statement freeze (public conclusion contracts complete)

The release scope is Theorems 1.7--1.10. Their proposition-valued conclusion
contracts now compile. Continue translating every supporting statement
literally enough that endpoint conventions, multiplicities,
uniformity, exceptional sets, and numerical constants remain visible. Record
every deliberate representation change in the crosswalk before proof work.

## Phase 4 - proof implementation (active)

Build from definitions and reusable lemmas toward the frozen source-facing
contracts. Research probes may be used, but they must remain outside the
production import root. Do not substitute theorem-shaped assumptions for
missing mathematics.

The compiled analytic chain now reaches Proposition 2.3(i) and the full
`theta > 2/15` range of Tao's constant-length Proposition 2.3(iii). It retains closed endpoint
conventions, bounds rather than discards all higher prime powers, performs the
finite dyadic-to-prefix conversion, and handles `theta >= 1` by monotonicity.
The Baker--Harman--Pintz 2001 paper is now pinned and hashed, with Theorem 1
and the closing quantitative estimate located. Clause (ii) of Proposition 2.3
still requires a Lean proof: the source proof is a full Harman-sieve argument
using Watt's fourth-moment estimate, Dirichlet-polynomial decompositions,
one- and two-dimensional sieve asymptotics, role reversals, and numerical loss
bounds. The next parallelizable mathematical layer is the earliest downstream
Section 3/4/6 consumer that does not presuppose this missing theorem. A
density-zero statement remains an inadequate replacement for the proved fixed
power saving.

The exact `VB¹` squarefree-cube sum now has its full source asymptotic.
Termwise domination controls the accumulated floor error, dominated
convergence produces the squarefree `b⁻³ᐟ²` limit, and the unique
square-times-squarefree decomposition identifies its constant as
`ζ(3/2)/ζ(3)`. The remaining Theorem 1.8 work is the nontrivial-`VB` upper
bound through Theorem 2.5, Lemmas 2.10--2.11, and Lemmas 3.1--3.2.
The first, elementary `H<N` clause of Lemma 3.1 is now proved for `N≥1`.
The positive-start hypothesis is necessary under the literal definitions:
`{1}` (`N=0,H=1`) is powerful. The remaining subexponential length estimate
is the first consumer of the still-unformalized Theorem 2.5.
Lemma 3.2's arithmetic extraction is now formalized independently: removing
exactly the exponent-one primes leaves a powerful core, and global
powerfulness forces every removed prime to be at most `H`. The coefficient is
squarefree and divides `H!`; any two positions yield the exact relation
`an+h=bm`. Its quantitative step is now formalized too: the coefficient
product divides an explicit small-prime envelope, finite Abel summation plus
Chebyshev bounds its logarithm by `C H log H`, and averaging separately on two
interval halves selects distinct coefficients at most `H^(3C)`. Lemma 3.2 is
therefore complete. The exact finite reindexing for Corollary 2.11 is also
complete. Lemma 2.10 now has its squarefree-discriminant reduction, literal
quadratic norm encoding, the full square-discriminant divisor bound, and the
norm-one Pell action on fixed-norm fibers. Exponential growth and the exact
logarithmic count of coordinate-bounded fundamental-unit powers are now
proved. Equality of principal ideals is also proved equivalent to norm-one
orbit membership on each nonzero `ℤ[√D]` norm fiber. The first
maximal-order comparison is now complete: the concrete quadratic field and its maximal
order are constructed, `ℤ[√D]` embeds injectively, fixed-norm points map to a
finite ideal-divisor set whose fibers are maximal-order unit classes, and the
degree-two at-most-two prime-splitting estimate is instantiated for every
rational prime. The next honest boundary is the multiplicative `d(|N|)²` cardinal bound
and quantitative height control for the full maximal-order unit group. Theorem 1.8
additionally still needs Theorem 2.5 and the
remaining Corollary 2.11 dyadic/interpolation count.

The other newly isolated dependency is Erdős--Selfridge Theorem 1, whose
square case controls the factorial-squarefree-component fibers in Theorem
1.10. Its original 1975 paper is pinned and hashed. No completed Lean proof
was found: the otherwise relevant `formal-conjectures` declaration contains
`sorry`, so this theorem must be recursively formalized here (or imported only
from a future immutable, audited proof release).

## Phase 5 - release engineering

When real endpoints exist, add:

- a production root;
- `Audit.lean` with permitted-axiom enforcement;
- exact source and dependency closure checks;
- zero-diagnostic builds and forbidden-token scans;
- a truthful reproduction manifest and architecture update.

## Non-goals and non-claims

- treating the frozen Gafni--Tao closure as a proof of a Tao theorem;
- changing nodes 71 or 74;
- claiming a result about the Riemann Hypothesis.
