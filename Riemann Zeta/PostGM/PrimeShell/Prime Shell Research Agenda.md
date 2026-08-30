# Prime Shell Research Agenda

## 1. Corrected objective

The Prime Shell objective is to determine whether known unconditional prime information beyond the classical length-`T` diagonal range can be inserted into the exact Alpoge-Furman/Zeta23 prime-side trace calculation and yield a genuinely new zero-distribution theorem.

The first proposed mechanism is a disconnected frequency region: retain the proved support-one block and add a high shell beginning only where a known arithmetic estimate reaches the resonant prime-pair shifts. This avoids pretending that every frequency immediately above one has been controlled.

The program is not a claim of progress toward RH. Even density one of simple critical-line zeros would leave open the possibility of infinitely many off-line zeros. Pair-correlation information beyond support one does not by itself supply an exceptional-zero rigidity theorem.

## 2. What is already known, and what is not

Alpoge-Furman define

\[
\mathcal M[u_1,u_2]
=
\iint_{I\times I}\Phi(\tau-\tau')^2u_1(\tau)u_2(\tau')\,d\tau\,d\tau'
\]

and decompose the full prime-side quantity in equation (5.10). Proposition 5.4 evaluates

\[
\mathcal M[P_X,P_X]
=
\frac{T}{\pi}\sum_{n\le X}\frac{\Lambda(n)^2}{n}g(\log n)
+O_\chi(L^2X).
\]

The paper explicitly identifies `X <= T` as the current boundary: when `X` is substantially larger than `T`, the off-diagonal prime sum is no longer dominated by the diagonal and prime-pair information is required.

Guth-Maynard Corollary 1.4 gives an almost-all short-interval prime theorem for lengths

\[
y\in[X^{2/15+\varepsilon},X^{0.99}],
\]

with an exponentially small exceptional set and error. It is not merely a consequence of the headline `30/13` exponent in the formal sense needed here. The published proof also invokes a near-one density estimate with logarithmic control, a Vinogradov-Korobov zero-free region, and explicit-formula/mean-square arguments. Those dependencies must remain visible if the source theorem is later formalized.

Matomaki-Radziwill-Tao Theorem 1.3 is a stronger fallback at a more distant scale: for almost all shifts in an interval of length `H >= X^(8/33+epsilon)`, it gives the expected singular-series asymptotic for `sum Lambda(n)Lambda(n+h)` with arbitrary logarithmic saving.

Phase I settles the first version of that question negatively. The exact dyadic source kernel is two-variable, depending on both `n` and `h`; it is not a scalar function of `h`. A collapsed prefix asymptotic can control an anchored scalar component, but not the separately exposed variation remainder without additional arithmetic information.

## 3. Exact first research question

After dyadically localizing `n,m` and setting `m=n+h`, the exact source contribution is

\[
\sum_N\sum_h\sum_n K_{N,T}(n,h)a_n a_{n+h}.
\]

It retains the actual weights, endpoints, normalizations, orientations, and remainder inherited from the trace. Anchoring at `n=N+1` gives the exact identity

\[
\sum_h K^*_{N,T}(h) C_N(h)+R_{\mathrm{var}},
\]

where both `K*` and `R_var` are explicit. The second term is not a disposal error: it is the information discarded by collapsing the `n` coordinate.

Define the cumulative correlation

\[
A_N(H)=\sum_{1\le h\le H}C_N(h).
\]

The Phase I question was:

> Are the size, variation, and localization properties of `K_{N,T}` strong enough that a uniform asymptotic for `A_N(H)` on the relevant range determines the weighted sum to the error demanded by the spectral consumer?

It has been settled by both sides of the ledger. `finite_abel_identity` and `abs_weighted_sum_le_of_prefix_bound` prove the scalar Abel transfer. `all_shift_prefixes_insufficient_for_nonconstant_two_variable_kernel` proves that all collapsed prefixes can vanish while a two-row kernel functional is nonzero whenever the rows differ. Thus the collapsed-prefix route fails unless one additionally proves exact row constancy, an `n`-localized/rectangle-prefix correlation estimate, or a direct bound on `R_var`.

This verdict does **not** include a concrete theorem that the AF taper's kernel differs at a named numerical tuple. Instead, the unconditional necessary-condition theorem makes the burden exact: a prefix-only consumer would have to prove row constancy. No such source identity is present in AF or Zeta23, and the source decomposition retains the variation term explicitly.

## 4. Arithmetic transfer ledger

The identity behind the GM route is, subject to an explicit endpoint convention,

\[
\sum_{1\le h\le H} C_N(h)
=
\sum_{N<n\le 2N}\Lambda(n)\bigl(\psi(n+H)-\psi(n)\bigr).
\]

Turning GM Corollary 1.4 into a usable bound requires each of the following:

1. convert the published `pi` statement to the required `psi`/von Mangoldt statement;
2. bound prime powers uniformly;
3. translate real/integer interval endpoints exactly;
4. apply the almost-all statement at the required family of lengths, not just one fixed length;
5. control the contribution of exceptional `n` after weighting by `Lambda(n)`;
6. make all dyadic and smoothing losses explicit;
7. preserve an error strong enough for the trace normalization;
8. prove the scale relation with a strict epsilon margin.

None of these is discharged by naming the GM zero-density theorem.

## 5. Scale ledger

For `n ~ N`, the phase difference behaves as

\[
T\log(1+h/n)\asymp Th/N.
\]

Thus the resonant length is `H_res ~ N/T`. If `N=T^alpha`, then

\[
H_{res}=N^{1-1/\alpha}.
\]

For GM, require

\[
1-1/\alpha > 2/15,
\]

with room for all epsilons, so the candidate shell begins strictly beyond `alpha=15/13`.

For MRT, require

\[
1-1/\alpha > 8/33,
\]

so the fallback shell begins strictly beyond `alpha=33/25`.

These computations locate candidate scales only. They neither prove that the disconnected shell is admissible nor evaluate the trace.

## 6. Three feasibility gates

### F1 - Kernel compatibility — Phase I verdict: FAIL for collapsed prefixes

The proposed cumulative interface does not control the exact two-variable trace kernel by itself. The weakest stronger input currently isolated is a direct bound for `dyadicKernelVariationRemainder`; an `n`-localized/rectangle-prefix estimate is a more arithmetic alternative. MRT's almost-all fixed-shift theorem is therefore the next justified source to test, but it has not yet been shown to meet this exact weighted consumer.

### F2 - Disconnected-shell admissibility

Pass only if a low block plus separated high shell is realized by the actual test-function/Gram construction, all positivity and Fourier constraints survive, and every cross term is evaluated or bounded. Frequency separation alone is not a proof that the cross term is negligible.

### F3 - Consumer value

Pass only if a narrowly stated arithmetic hypothesis, inserted into the actual trace and inertia consumer, yields a mathematically meaningful theorem outside a precisely defined support-one certificate class. Formalizing GM short intervals or MRT is unauthorized until this price test passes.

## 7. Numerical benchmark correction

The Zeta23 `PairCeiling` files establish a kernel-checked implication from a displayed `EnclOK` enclosure hypothesis. The repository explains that the concrete enclosures for the 256-periodic law came from external interval arithmetic. The cited certificate data and reproduction path are not part of the released Comparator topic.

Therefore `0.6818287...` may be used as:

- a conditional or externally certified comparison target;
- a heuristic optimization target; or
- an unconditional benchmark only after the exact `EnclOK` certificate is independently reproduced or a new internal proof is supplied.

The primary success criterion is consequently structural: a new unconditional theorem must use arithmetic information outside support one and lie outside an explicitly defined support-one certificate class. A promised decimal is not part of the initial contract.

## 8. Formalization architecture

### Stage A - Separate reproduction

Reproduce Zeta23 `v1.0` at commit `3635e748...` using its Lean `v4.33.0-rc2` toolchain. Preserve its Comparator statement surface. Record the fact that the frozen GM project uses Lean `v4.30.0` and a different Mathlib commit.

### Stage B - Source-faithful decomposition

Work in a separate Zeta23-compatible extension. Add no import to the GM root. Expose the exact prime-prime term and recover the existing theorem as a regression test.

### Stage C - Conditional feasibility theorem

A conditional theorem may accept a narrowly stated finite arithmetic estimate if it is visibly weaker than the zero conclusion and the proof genuinely transforms it through the kernel. Do not declare an axiom. Do not use a hypothesis that mentions zero counts or the desired trace bound itself.

### Stage D - Native arithmetic proof

Only after F1-F3 pass, formalize the selected source input. If the GM route is selected, the implementation lives in this post-GM program or a separate library and consumes the frozen GM release as an input boundary; it does not rewrite the frozen proof.

### Stage E - Audited consumer and release

Replace the conditional input, run explicit axiom audits, ensure zero warnings, reproduce trusted statements through Comparator or an equivalent two-sided statement check, and tie the result to an immutable commit.

## 9. Repositories and reusable resources

The detailed pins and links are in [Prime Shell Sources](Prime%20Shell%20Sources.md). The most relevant code is:

- Anthropic `formal-math/zeta23`: exact prime side, finite compression, inertia/rank assembly, and Comparator contracts;
- PrimeNumberTheoremAnd: explicit formula, Mellin, zeta, and zero-free/PNT infrastructure already familiar to the GM project;
- Mathlib: measure/integration, Fourier analysis, finite sums, linear algebra, asymptotics, and arithmetic support;
- Lean Comparator: independent statement-equivalence and permitted-axiom checking;
- Palomar conventions: a public challenge/solution boundary for future release.

No public Lean repository located in this audit already proves the desired Prime Shell prime-pair consumer or formalizes the GM/MRT transfer required here. Existing repositories reduce infrastructure cost, not the research obligation.

## 10. Kill rules

Terminate the current route, while preserving proved decompositions, if:

1. F1 proves that the exact kernel requires fixed-shift Hardy-Littlewood or comparably strong phase information;
2. F2 proves that the disconnected shell cannot be represented by the actual test family;
3. the strongest plausible arithmetic oracle yields no meaningful theorem in F3;
4. the required source error is stronger than GM or MRT supplies;
5. a toolchain port becomes the dominant cost before consumer value is established;
6. the result merely repackages support-one information;
7. the proposed theorem assumes zero statistics or the desired zero conclusion.

A killed route must record the exact obstruction, strongest theorem reached, and conditions under which reconsideration would be rational.

## 11. Completion levels

- **Phase I complete:** pinned reproduction, exact crosswalk, exact kernel, exact arithmetic interface, and rigorous F1 PASS/FAIL.
- **Feasibility complete:** F1, F2, and F3 have rigorous verdicts.
- **Analytic route complete:** a full source-faithful informal proof meets the consumer budget.
- **Formal theorem complete:** the native arithmetic input, trace theorem, spectral consumer, and zero theorem are kernel-checked with clean audits.
- **Publication complete:** immutable release, independent statement verification, exposition, and external mathematical review exist.

Phase I is complete with the negative verdict above. No feasibility, analytic-route, formal-zero-theorem, or publication completion is claimed.
