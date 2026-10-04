# Research agenda and current status

**4 October 2026 — PLANNING ONLY; 0/20 implementation gates complete.** The owner requested setup, not conversion. No proof goal has been activated; all DWWZ-01 through DWWZ-20 remain OPEN.

## Work completed in this setup

Identified and read the primary paper's five sections and reference list using its HTML and frozen TeX, including both full theorem statements, all seven lemmas and Proposition 4.1. Archived the original PDF and source archive with extracted source. Examined the cited Granville–Soundararajan mean-value and zero-forcing inputs in journal/preprint versions and located the author-hosted exponential-sum chapter. Searched current paper metadata, author publications, web and GitHub implementation evidence, three live upstream repositories, and relevant local interfaces. Prepared the scaffold, inactive goal prompt and source-integrity runner.

This is a literature/interface investigation, not a complete semantic audit of existing libraries or a new proof. The [Sources](Dong-Wang-Wang-Zhang%20Sources.md) document records limits and dated negative results.

## First analytic priority after activation

The most consequential apparently missing input is the uniform mean-value/twist/Lipschitz package needed for **Lemma 2.2**. Its outputs drive the Gaussian lower bound and hence the main inverse theorem. No equivalent theorem was located in the searched local or public Lean sources. This is a search result, not a claim that the theorem is inaccessible or impossible to formalize.

Aim first at the smallest genuine specialization for the completely multiplicative function `n ↦ n^(it)`, with the actual maximizing twist. DWWZ-05 must supply the analytic reason a large sum varies slowly after twisting; DWWZ-06 then assembles the exact uniform estimates. Do not settle for a generic implication assuming those estimates.

Independent branches with useful existing infrastructure are: zeta/xi zero sums (DWWZ-04/08/09/11), the Gaussian identity including its pole (DWWZ-07/10), and the classical large-x estimate (DWWZ-15). Reusing those branches should avoid reproving foundations, but they do not eliminate the need for DWWZ-05.

## Minimal remaining-obligation DAG

1. DWWZ-01/02/03/04: compatible package, exact statements and faithful objects.
2. DWWZ-05 → 06: analytic mean-value inputs → actual twist selection, global-in-y Lipschitz and comparison.
3. DWWZ-04 → 08 → 09/11: multiplicity-faithful xi product/convergence → zeta growth from zeros and weighted-zero upper bound; DWWZ-07 supplies the small-height bound.
4. DWWZ-03/07 → 10: actual shifted-series Gaussian identity, contour shift and residue.
5. DWWZ-06/07/09/10 → 12: weighted-zero forcing from the original large sum.
6. DWWZ-04/11/12 → 13 → 14: actual near/far split → T1 with a common center.
7. DWWZ-03 → 15; DWWZ-14/15 → 16: large-x cancellation plus local-window contradiction → full T2.
8. DWWZ-17/18/19/20: exact regressions, dependency/coverage audits, both BATs and synchronized release evidence.

These are future obligations, not instructions to start them during template creation. Keep this DAG short; split a gate into helper lemmas only when its active proof needs them.

## Route selection and stopping source searches

Primary route: the paper's adaptation of Granville–Soundararajan. For DWWZ-05, compare the journal's Theorems 2b/4 and Lemma 7.1 with the precise Section 2 restatement in the later zero-forcing paper. The two versions' maxima and Euler-product conventions require a bridge, not textual substitution.

If formalizing the general multiplicative-function theory becomes disproportionate, investigate a direct proof of the needed specialized twist/Lipschitz estimate. For DWWZ-10, a vertical-line Mellin/contour argument is a possible alternative to parameter continuation, provided it proves the exact same integrals and residue. For DWWZ-15, a finite third-derivative estimate can replace the exponent-pair abstraction if its uniform range is proved. These are prospective alternatives, not proved repairs.

Do not continue broad source hunting merely because a proof is difficult. Reopen it for a newly identified theorem, a concrete missing cited input, or a newer primary revision. Work on actual analytic bounds and consumers. Bibliography growth, scalar comparisons, fresh module families and conditional wrappers are not replacements for closing gates.

## Regression design to retain

Test the `n=0` exclusion; floor endpoints; `x<1`; both signs of `t`; repeated zeros; pole exclusion; `λ=1/2`; unbounded `a`; the open disk versus closed window; a single `φ` before all `L`; empty admissible intervals; the exact residue sign/denominator; Gaussian parameter distinct from height; small versus large x at `sqrt T`; nonintegral dyadic endpoints; `ε` strictness; and `K(A)` independent of `δ`. Preserve any counterexample or source correction as a permanent regression.

## Acceptance authority

The [Checklist](Dong-Wang-Wang-Zhang%20Checklist.md), [Architecture](Dong-Wang-Wang-Zhang%20Architecture.md) and this agenda must always report the same gate statuses. Source Contract controls mathematical outputs. Reproduction Manifest controls evidence claims. The ready [Goal Prompt](Dong-Wang-Wang-Zhang%20Goal%20Prompt.md) includes maintenance of the paper BAT and foundation BAT. Recovery-record files are never a task dependency.
