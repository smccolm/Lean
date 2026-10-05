# Frozen source contract

**Implementation status, 5 October 2026:** both frozen contracts below now have exact-type-checked public Lean proofs, `large_zeta_sum_forces_zero_disk` and `local_zero_windows_force_zeta_sum_cancellation`. Both sequential BATs, transitive audits and exact semantic acceptance passed; all twenty gates are complete. The original 4 October specification, including its historical planning-status wording, is retained verbatim below; it is not the current implementation status.

Source: [arXiv:2608.31060v1](https://arxiv.org/html/2608.31060v1), [local original TeX](Sources/DongWangWangZhang-v1-source/main.tex). Recorded 4 October 2026. **Mathematical specification only; not stated or proved in Lean.** The immutable source bytes, not a paraphrase, resolve any discrepancy below.

## Actual objects

For real `x,t`, use the finite sum over positive integers

\[
S(x,t)=\sum_{1\le n\le x}\exp(it\log n).
\]

It is zero for `x<1`. A future Lean definition must use the natural floor and omit `n=0`; prove its equality to the source's complex-power convention. Nontrivial zeros are actual zeros of Mathlib's `riemannZeta`, in `0<Re ρ<1`, counted with analytic vanishing order. Neither the totalized value at the pole nor distinct-zero cardinality is a substitute.

Write `Z(D)` for this multiplicity-weighted count in a bounded region `D`. Establish finiteness, independence of an enclosing rectangle, conjugation invariance, and monotonicity. Infinite weighted zero sums must use the same multiplicity convention and have proved convergence; Lean's default value of a nonsummable `tsum` is not a proof.

## T1 — Theorem 1.1 (`thm:main`)

There exist absolute `c>0` and `T₀≥3` such that, for all real `T,t,x,N` satisfying

\[
T\ge T_0,\quad T\le |t|\le2T,\quad
e^{\sqrt{\log T}}\le x\le\sqrt T,\quad
|S(x,t)|=x/N,\quad 1\le N\le(\log x)^{1/100},
\]

there exists a real `φ` with `|φ−t|≤cN` such that **for every** real `L` satisfying `cN⁶≤L≤(log x)/2`,

\[
 Z\!\left(\left\{s:\left|s-(1+i\phi)\right|
       <\frac{L\log T}{(\log x)^2}\right\}\right)\ge L/360.
\]

Quantifier order: `∃ c,T₀; ∀ T,t,x,N; ∃ φ; ∀ L`. The center may depend on `x,t,N,T`, but not on `L`. The same `c` controls displacement and the lower admissible scale. The disk is **open**; the `L` interval and the displayed `T,x,N` bounds are closed. The count is a natural number compared, after coercion, with a real `L/360`. Both signs of `t` are included. Do not assume the interval of admissible `L` is nonempty.

## T2 — Theorem 1.2 (`thm:corollary`)

There is an absolute `C>0`. For each `A>0` there is a bound constant `K(A)>0` independent of `δ,ε,T,t,x`. For every fixed `0<δ≤1/4` there is `T₀(A,δ)≥3` such that for `T≥T₀(A,δ)`, `T≤|t|≤2T`, and

\[
\varepsilon>(\log T)^{-1/3},
\]

the following implication holds. If **every** real `u` with `|u−t|≤C(log T)^(1/100)` satisfies

\[
 Z\{s:\Re s\ge1-\delta,\ |\Im s-u|\le\delta\}
       \le \delta\varepsilon^2\log T/400,
\]

then, for all `T^ε≤x≤T^A`,

\[
 |S(x,t)|\le K(A)\,x/(\log x)^{1/100}.
\]

This is an unconditional proof of an implication with the paper's **explicit local zero hypothesis**, not an unconditional estimate at every height. The hypothesis is not RH. No upper restriction on `ε` belongs in the public statement: empty ranges are allowed. The zero window is closed in both coordinates. Although written as an unbounded right strip, its nontrivial zeros lie in `Re s<1`, so its count is finite. The strict lower bound on `ε`, the full polynomial range of `x`, and the distinction between `C`, `K(A)` and `T₀(A,δ)` must survive formalization.

## Supporting contracts and scope

The [crosswalk](Dong-Wang-Wang-Zhang%20Crosswalk.md) covers Lemmas 2.1, 2.2, 3.1–3.4, Proposition 4.1 and Lemma 5.1. Preserve these source statements even if a narrower, genuinely proved specialization or an alternate argument supplies a main-theorem input. Record exactly which support generality is implemented. No end theorem may assume Lemma 2.2, Proposition 4.1, T1, a zero-cluster assertion, or an equivalent certificate as an undischarged analytic premise.

Remark 1.3 (exceptional-set consequence using Guth–Maynard), the RH observation, and the discussion of Lindelöf and fixed-height asymptotics are supplementary, not extra main-theorem release gates. Before adding them as public corollaries, audit their complete ranges and constants independently. In particular, verify the stated density exponent against the precise source interval instead of inferring it from an informal graph edge.

Source repairs require a separate explicit record: immutable original, exact defect or counterexample, proposed correction, authorization, proof and permanent regression. No correction is authorized or claimed by creating this template. Keep all end statements frozen; a weaker statement is not completion.
