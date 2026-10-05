# Frozen source and intended mathematical contract

**PLANNING ONLY. No Lean statement or proof created.** The immutable edition is arXiv:2609.00537v1. `Sources/DhimanKadiriQuesadaHerrera-v1-source/AFE2026ago31.tex` is authoritative alongside the 37-page PDF. `Tools/source_labels.json` maps all active source labels to exact TeX line locations and the source hash. Resolve the Errata register at DKKH-01 before declaring an accepted formal contract. The original text remains frozen even when a corrected formal target is adopted.

## Objects and notation

Use Mathlib's actual `riemannZeta`, `Complex.Gamma` and `Complex.digamma`. For positive integer n, use principal complex powers with real-positive base; `e(u)=exp(2πiu)`. A source sum `a<n≤b` ranges over integers; a zeta partial sum uses positive integers and includes 1. Half-integer means `∃ k : ℤ, x=k+1/2`. The AFE assumptions force x,y positive. Every O* display means a literal absolute-value/norm inequality with coefficient one; it is not asymptotic notation.

Define the source χ factor as `χ(s)=2^s π^(s−1) Γ(1−s) sin(πs/2)`. Its valid functional equation is `ζ(s)=χ(s)ζ(1−s)` on the appropriate nonexceptional domain. The paper's reversed sentence in §2.5 is E02. At the AFE heights, `s≠1`; nevertheless prove all division and gamma-domain side conditions rather than relying on totalized operations.

The actual AFE2 remainder is

`E(σ,t,x,y) = ζ(σ+it) − Σ(1≤n≤x) n^(−σ−it) − χ(σ+it) Σ(1≤m≤y) m^(σ+it−1)`.

It must not be an arbitrary function supplied together with an assumed error bound.

## P8 — Theorem 8, weighted truncated Poisson

Primary label `thm-VDC`, PDF pp. 12–14. For `a<b`, positive continuous strictly decreasing f′, positive decreasing C¹ weight g, and integer `0≤N<f′(b)`, set `δ=1−(f′(a)−floor(f′(a)))` and

`R_N(a,b)=Σ(N≤ν≤floor(f′(a))) ∫[a,b] g(u)e(f(u)−νu) du`.

Prove `|Σ(a<n≤b) g(n)e(f(n))−R_N(a,b)|≤T_N(a,b)` with **every term** of `def-TNab` and its half-integer form `def-TNab-integer+1/2`. Part II adds the printed C² and derivative positivity/decrease assumptions and replaces the error by `def-TNab-partII` and `def-TNab-integer+1/2-partII`. Auxiliary `G`, `H`, `H_1`, `B`, `E_1`, `E_2` remain the actual source expressions, not free constants.

The source writes g(x) under a sum indexed by n: intended g(n) is E01. General-N phase shifting, the endpoint sawtooth convention, and the constant-weight non-strict boundary of the derivative assumptions must be resolved explicitly (E05–E06). Proving only N=0 or only half-integer endpoints is an incomplete P8.

## PB — Corollaries 0.1, 0.2 and 8.1

`cor-VDC` supplies the two g=1 half-integer bounds; `cor-thmVDC-partII` specializes δ=1/2. `Explicit_B_estimate` is the stationary dual-sum estimate with positive decreasing f′, `0<f′(b)<1`, three derivatives and the stated λ₂,h₂,λ₃,h₃ bounds. The phase is `f(xν)−νxν−1/8`, `f′(xν)=ν`, amplitude `|f″(xν)|^(−1/2)`. Keep `2.686/√λ₂`, the cubic-derivative term, `2/π log(f′(a)−f′(b))`, and the entire D_f expression including `1.251`. Implicit positivity of scale parameters needs an explicit valid formal domain.

## A1 — Theorem 9 and Corollary 0.3

`thm-AFE1`, PDF p.22. Intended positive-index contract, subject to E01:

`0<σ≤1`, `t≥t₀>0`, `c>1/(2π)`, `ct∈ℤ+1/2`, and

`|ζ(σ+it)−Σ(1≤n≤ct)n^(−σ−it)| ≤ m(c)(ct)^(−σ)`.

Let `u=1/(2πc)`. The exact source function is

`m(c)=c+(1+1/t₀)/π · (log(1+u)+γ−ψ(1−u)−1/[2(1+u)]−1/2)`.

The printed theorem excludes 1, whereas the proof includes it. Do not freeze that error as a required false goal. Review the proof's `x>1` restriction against the displayed general domain before closing A1 (E07).

For all real `t≥t₀≥14`, `cor:all_t` concludes the analogous sharp cutoff at t with `c₀ t^(−σ)`. With `N=floor(t₀)`, the exact `eq:def-c0` is the maximum of

`m((N+1/2)/t₀)`, `m((N+3/2)/(N+1))`, and `m(1−1/[2(N+1)])/(1−1/[2(N+1)])`.

Certify `c₀≤1.2552` at `t₀=14.13472` and `c₀≤1.2127` at `t₀=3·10^12`. The prose later says 14.13473; keep the advertised smaller threshold and prove it, or record a substantive correction. No hypothesis about verified zeta zeros is needed for either numerical parameter.

## A2 — Theorem 10, both error branches

`thm-AFE2`, PDF p.25: `1/2≤σ≤1`, `|t|≥t₀≥2π`, `x,y∈ℤ+1/2`, `x,y≥h≥3/2`, `2πxy=|t|`.

The proposed proof-consistent branch functions, **pending E03 resolution**, are

`E_direct(σ,h,t₀)=A₀(σ,h,t₀)+C₀(σ,t₀)B₀(σ,t₀)` and

`E_reflect(σ,h,t₀)=A₀(1−σ,h,t₀)C₀(σ,t₀)+B₀(1−σ,t₀)`.

For x≥y, the intended bound is

`|E|≤(log y/π+E_direct) (|t|/(2π))^(1/2−σ) y^(σ−1)`.

For x<y, it is

`|E|≤(C₀(σ,t₀)log x/π+E_reflect) x^(−σ)`.

The display `def-E0-all-x-y` reverses these E₀ assignments; the end of the proof and `AFE2.py` use the assignments above. Preserve the distinction. The source also writes signed t in fractional real powers while allowing negative t: use a proved positive-height reduction and conjugation bridge, not Lean's totalized real power of a negative base (E04).

Use **all** terms of `def-A0` (5.22), `def-B0` (5.23), `def-C0` (2.17), `eq:Ci` and `x₀=max(h,√(t₀/(2π)))`. These expressions are pinned by source hash and label, avoiding an error-prone second transcription of several multi-line formulas. Their actual definitions and equality bridges must appear in the later Lean contract.

## Numeric consequences and scope

`cor-AFE2` takes maxima over `σ∈[1/2,1]`; preserve dependence on h,t₀ and x/y branch. `cor-k-AFE2` has integer `1≤k≤50`, `h_k=floor(exp(k−1))+1/2`, `H_k=exp(k)` and `h_k≤min(x,y)≤H_k`. Its constants derive from `k/π+ε₀` or `k(1+δ₀)/π+ε₀` with the appropriate branch. Table 1, Tables 2–3, `eq:ek-largeK` and `eq:AFE2-simple` are finite certification obligations. Exact source decimals and thresholds are retained; a rounded-down approximation is not automatically a valid upper bound (E08).

The author script's k=51..150 output, improvements to Patel–Yang's final subconvexity constant, elimination of half-integer AFE2 cutoffs, elimination of all logarithmic loss, RH itself, new zero-density bounds and a full Simonič/Riemann–Siegel formalization are outside this contract. They may be separate extensions only after the stated outputs are complete and separately scoped.
