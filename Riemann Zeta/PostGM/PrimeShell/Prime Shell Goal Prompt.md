# Prime Shell Persistent Goal Prompt

Use the following prompt for the next turn.

```text
Create a persistent goal to complete Prime Shell Phase I (Prime Shell Shitlist PSH-01 through PSH-06) without modifying the frozen Guth-Maynard proof.

The frozen GM boundary is commit 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, tag gm-foundation-freeze-v1.0.1, Lean v4.30.0. Treat every existing RiemannZeta/ Lean module and its GM public theorem chain as read-only. All new code, patches, manifests, logs, and research notes must live under PostGM/PrimeShell/ or in a separately pinned temporary checkout whose exact state is recorded. Do not import the experiment into RiemannZeta.lean.

Use the published Alpoge-Furman paper arXiv:2608.13637v2, Guth-Maynard arXiv:2405.20552v2, and the exact Anthropic Zeta23 release as authoritative source material. Reproduce Anthropic formal-math tag v1.0 at commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510 with Lean v4.33.0-rc2 and Mathlib 51e6992efd06126df61a496bebf8f49482a4e129 before changing it. Run its documented build, axiom audit, and Comparator checks and record the exact results. Do not work from moving main.

Then complete these tasks in order:

1. Produce an exact paper-to-Lean crosswalk for equation (2.7), equations (5.10)-(5.11), Proposition 5.4, Theorem 5.7, and the Section 7.2 support-one obstruction. Name exact declarations, files, theorem types, normalizations, Fourier conventions, intervals, and endpoint choices.
2. In an isolated Zeta23-compatible extension, expose the exact prime-prime term M[P_X,P_X] as a proved equality whose diagonal, resonant same-sign off-diagonal, opposite-sign off-diagonal, boundary truncation, and remainder terms are separately accessible. Recover the existing X <= T prime-term theorem from this decomposition as a regression theorem.
3. Dyadically localize the dangerous contribution and prove the exact m=n+h rewrite

   sum_N sum_h K_{N,T}(h) C_N(h) + remainder,

   with C_N(h) the actual weighted von Mangoldt correlation produced by the source calculation. Keep the literal K_{N,T}; prove its support, signs, size, smoothness or discrete variation, resonant range, tails, endpoint corrections, and every uniform error. Do not replace it by an unspecified bounded weight.
4. State, but do not assume as an axiom and do not yet prove from scratch, the narrowest finite arithmetic estimate that Guth-Maynard Corollary 1.4 could legitimately provide. Derive its exact shape from the published pi statement, explicitly accounting for pi-to-psi conversion, prime powers, the exceptional set weighted by Lambda(n), simultaneous interval lengths, dyadic subdivision, endpoints, epsilon margins, and quantitative error. Record the additional published dependencies in GM Section 13.2, including the near-one logarithmic density input and Vinogradov-Korobov zero-free region.
5. Settle F1 rigorously. Either prove a kernel-checked summation-by-parts/Abel transfer showing that this cumulative prefix estimate controls the exact K_{N,T}-weighted correlation within the prime-trace consumer's required error, or prove a precise no-go theorem/counterexample showing that prefix information is insufficient and identify the weakest stronger input needed. A heuristic, a scale comparison, or an abstract cardinality bound detached from the exact kernel is not completion.
6. Prove the scale consequences with strict epsilon margins: for N=T^alpha, H_res asymptotic to N/T, and the GM overlap only for alpha strictly beyond 15/13 after all losses. Do not call this a support theorem.

Completion of this goal requires:

- unchanged pinned Zeta23 reproduction with exact logs and pins;
- exact source crosswalk;
- exact prime-prime decomposition and recovery of the current theorem;
- exact dyadic shift kernel and error ledger;
- exact narrow GM cumulative-correlation interface;
- a theorem-level F1 PASS or FAIL verdict;
- no edit to the frozen GM Lean source or public contracts;
- no sorry, admit, project axiom, unsafe bypass, theorem-equivalent hypothesis, hidden oracle, or toy replacement;
- explicit axiom audits of every new public theorem;
- zero Lean warnings and linter diagnostics in the isolated build;
- synchronized updates only to PostGM/PrimeShell documentation after the verdict is proved; and
- the mandatory final commit-message update in push_to_github.bat, without running that script.

Do not continue to disconnected-shell optimization, do not formalize the full GM short-interval theorem, and do not claim a new zero theorem during this Phase I goal. If F1 fails rigorously, mark Phase I complete with the GM-prefix route killed, preserve the exact decomposition, and state whether the MRT almost-all fixed-shift theorem is the next justified input. Keep the program name Prime Shell and do not describe it as a path to the Riemann Hypothesis.
```
