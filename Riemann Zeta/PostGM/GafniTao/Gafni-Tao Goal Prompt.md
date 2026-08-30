# Whole-proof goal prompt

Copy the text below into the next turn.

---

Your goal is to complete the entire Gafni-Tao exceptional-interval
formalization, Shitlist GT-00 through GT-26, without modifying the frozen
Guth-Maynard proof. The frozen boundary is tag
`gm-foundation-freeze-v1.0.1`, commit
`2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, Lean `v4.30.0`. Treat every
`RiemannZeta/` source module and its public theorem chain as read-only. Put all
new Lean source, dependencies, source snapshots, manifests, audits, runners,
logs, and documentation under `PostGM/GafniTao/`, using a separate Lake package
pinned to the frozen foundation. Do not import the experiment into
`RiemannZeta.lean` and do not work from a moving dependency revision.

Treat Gafni-Tao arXiv:2505.24017v1 as the authoritative target, and Guth-
Maynard arXiv:2405.20552v2, Heath-Brown's 1979 zero-density/additive-energy
paper, Ford's Vinogradov-Korobov bounds, Turan Theorem 38.2, Pintz's 2023
near-one density paper, Davenport Chapter 17, Tao-Trudgian-Yang
arXiv:2501.16779, and a pinned ANTEDB snapshot as authoritative upstream
sources for the exact results they contain. Save and SHA-256 hash the source
artifacts before coding. Use Mathlib, audited PNT+ infrastructure, and the
frozen GM declarations where their theorem types match. No paper, database,
comment, executable calculation, or theorem name is proof evidence until a
Lean theorem consumes it.

The required mathematical output is the complete source-faithful proof of
Gafni-Tao Theorems 1.1, 1.2, and 1.3. Define the exact Lebesgue-measurable set

`E_delta(X,theta) = {x in [X,2X] :
 |sum_{x<n<=x+x^theta} Lambda(n)-x^theta| >= delta*x^theta}`,

the extended exceptional exponents `mu_delta(theta)` and `mu(theta)`, the
actual multiplicity-weighted zeta zero density exponent `A(sigma)`, the exact
four-zero tolerance-one count

`N*(sigma,T) = # {(rho1,rho2,rho3,rho4) in Z(sigma,T)^4 :
 |gamma1+gamma2-gamma3-gamma4| <= 1}`

with product analytic multiplicity, and its exponent `A*(sigma)`. Preserve the
empty-supremum `-infinity` convention. The definition of `mu_delta(theta)` must
use the paper's fixed-power eventual bound
`|E_delta(X,theta)| <<_{delta,theta} X^xi`, with no inserted epsilon loss;
`A` and `A*` use their source `for every epsilon>0` bounds. Prove ergonomic
interfaces equivalent to these extended-real definitions and the paper's
countable diagonalization in `delta`; do not replace the source objects with
independently supplied functions, distinct-zero sets, sampled exceptional
points, or theorem-equivalent certificates.

Prove, in source order, every entry bridge and analytic step: the real-endpoint
Chebyshev/von-Mangoldt identity; the local cover and Brun-Titchmarsh replacement
with `tau=X^(1-theta)`; the sharp truncated explicit formula at
`T=J*log(X)^2*tau` including sign, multiplicity, pole, trivial-zero,
prime-power, endpoint and `O(x log^2(x)/T)` terms; equations (2.3)-(2.4); the
Vinogradov-Korobov zero-free region (2.6); the near-one logarithmic density
bound `N(1-eta,T) <= T^(C eta^(3/2))*log(T)^B` with no `T^epsilon`
substitution; Lemma 2.1; Lemma 2.2; the nonnegative log-scale bump,
complexified Fourier transform, uniform decay and exact `c_rho`; Lemma 2.3
with unit local-zero count; the pair-count function, double counting, Schur
test and exact bridge to `N*`; and Lemma 2.4.

Then formalize the half-open `J`-strip partition and equation (2.7), explicitly
handling the right-edge, small-`A`, `L2`, and `L4` alternatives. Maintain a
complete dependency and exponent ledger for `delta`, `theta`, `epsilon`, `J`,
`X`, `tau`, `T`, logarithms, endpoints, local-cover multiplicity, and all
`2/J`, `4/J`, and `o(1)` losses. Take the limits in the paper's order. Retain
the mandatory `inf_{epsilon>0}` in Theorems 1.2-1.3; do not assume continuity
of `A`.

The principal refined theorem must be equivalent to

`mu(theta) <= inf_{epsilon>0}
  sup_{0<=sigma<1, A(sigma)>=1/(1-theta)-epsilon}
    min((1-theta)*(1-sigma)*A(sigma)+2*sigma-1,
        (1-theta)*(1-sigma)*A*(sigma)+4*sigma-3)`.

Also prove the paper's alternate `max(1-theta,...)` form and the ordinary
second-moment Theorem 1.2 as exact corollaries. Prove Theorem 1.1's all-
interval and almost-all-interval consequences for a uniform ordinary density
exponent, including the bridge from `mu(theta)<1` to density zero.

Next consume the real frozen theorem
`RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native`, rather than
projecting or restating it, to obtain the `A0=30/13` thresholds
`theta>17/30` and `theta>2/15`. Recursively formalize the exact published
Pintz ordinary-density segment used for the `sigma<=23/24` cutoff and the
Heath-Brown `A*` estimates required around `sigma=7/10`, with the source's
multiplicity and endpoint conventions. Prove the exact native sample
corollaries

`mu(17/30) <= 7/12`

and, with an explicit quantified sufficiently-small range,

`0 < Delta -> mu(2/15+Delta) <= 1-9*Delta/13`.

If claiming reproduction of the complete Section 3 best-known curve, pin the
exact ANTEDB commit, formalize every invoked Tao-Trudgian-Yang/Heath-Brown
piece, and kernel-check an exact rational/algebraic piecewise optimizer. A
floating-point computation or plotted graph is only a cross-check and cannot
close a theorem.

When any dependency is unavailable, recursively formalize the faithful
published statement and return to the parent theorem. Continue through
analytic prerequisites, integrations, order-theoretic infima/suprema,
arithmetic comparisons, and final consumers. Do not end the goal after a
definition, conditional interface, infrastructure lemma, source crosswalk,
focused build, axiom audit, numerical experiment, documentation update, or
one corollary. Do not convert remaining implementation into another plan or
phase. The exact Shitlist acceptance theorem remains the stopping criterion.

Completion requires all of GT-00 through GT-26: exact public Theorems 1.1-1.3;
the two native Section 3 bounds; actual consumption of frozen GM and the
formalized zero-energy inputs; no `sorry`, `admit`, project axiom, unsafe
bypass, `native_decide`, theorem-equivalent hypothesis, hidden oracle, or toy
replacement; explicit `#print axioms` audits showing only permitted
Lean/Mathlib logical axioms; every production module imported by the isolated
root; zero Lean warnings and linter diagnostics; a warning-failing isolated
principal runner; forbidden-token and dependency scans; exact source hashes
and reproduction logs; and synchronized updates to the Gafni-Tao architecture,
research agenda, Shitlist, README, crosswalk, and audit only after the
corresponding theorem is genuinely proved.

Do not modify the frozen GM proof, do not run `push_to_github.bat`, and do not
put the push script into any build or CI workflow. Periodically update the
`Suggested commit message` line in `Gafni-Tao Research Agenda.md` to describe
the latest genuinely completed milestone; the owner will pass that message to
the simple push script. Do not describe this program as a path to the Riemann
Hypothesis and do not claim publication, peer review, canonicality, new
mathematics, or complete formalization until the literal acceptance gates
establish that claim.

If the requested source theorem is inconsistent as stated, completion may
instead be a kernel-checked counterexample or contradiction that pinpoints the
false statement and a source-level erratum. Difficulty, proof length, missing
library convenience, or a first failed tactic is not such a result and is not
a reason to stop.

---
