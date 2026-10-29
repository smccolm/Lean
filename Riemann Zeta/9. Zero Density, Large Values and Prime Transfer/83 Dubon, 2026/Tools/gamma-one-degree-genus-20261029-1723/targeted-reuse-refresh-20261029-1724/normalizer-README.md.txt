# Normalizers of congruence subgroups in Lean 4

A Lean 4 / Mathlib formalization of the normalizers in SL₂(ℝ) of congruence subgroups Γ ≤ SL₂(ℤ), and of the
groups Nor(Γ)/Γ of modular automorphisms of the corresponding modular curves: X₀(N), X₁(N), X(N), X_Δ(N), the
Cartan modular curves, and general modular curves X_H; and of Helling's theorem on the maximal subgroups of SL₂(ℝ)
commensurable with SL₂(ℤ).

* **183 theorems, all proved.** No `sorry`. Every theorem depends only on the standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
* The definitions and statements of each part were written and **frozen before any proof was written**. The proofs
  did not change them; [`frozen/`](frozen) and the scripts in [`scripts/`](scripts) let you check this.
* The ten files in [`Challenge/`](Challenge), one for each part (Part 3 in two), state the 183 theorems, with
  `sorry` as proofs, together with every definition they use, over Mathlib alone; Parts 1, 2, 5, 6, 7, 8 and 9
  and Part 3 without B₀(N) are entries of the [Palomar](https://palomar-registry.org) registry.
  [Comparator](https://github.com/leanprover/comparator) checks that the repository proves exactly these statements
  about exactly these definitions (see
  [Checking with Comparator](#checking-with-comparator)).
* About 24,000 lines of Lean, on Lean v4.35.0-rc3 and Mathlib v4.35.0-rc3, using Lean's module system.

Author: Filip Najman.

I thank David Kurniadi Angdinata for his help with Comparator, in particular for making the challenge
self-contained ([#1](https://github.com/F-Najman/normalizer-lean/pull/1)), so that Comparator also checks the
definitions.
I thank Maarten Derickx for suggesting the formalization of Helling's theorem (Part 9).

## Contents

* [Overview](#overview)
* [Conventions](#conventions)
* [How to read the statements](#how-to-read-the-statements)
* [Part 1. B(N) = Nor(Γ₀(N))/Γ₀(N)](#part-1)
* [Part 2. Γ_Δ(N), Γ(N) and ±Γ₁(N)](#part-2)
* [Part 3. More on Γ_Δ(N), and B₀(N)](#part-3)
* [Part 4. The order for X(N)](#part-4)
* [Part 5. Cartan modular curves](#part-5)
* [Part 6. General modular curves X_H](#part-6)
* [Part 7. The normalizer of Γ_Δ(N) for every Δ](#part-7)
* [Part 8. Mixed level: Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂)](#part-8)
* [Part 9. Helling's theorem](#part-9)
* [Building and checking](#building-and-checking)
* [Repository layout](#repository-layout)
* [Notes on the sources](#notes-on-the-sources)
* [References](#references)
* [License](#license)

## Overview

| part | statements | # | content |
|---|---|---|---|
| [1](#part-1) | [`NormalizerLean/Statements.lean`](NormalizerLean/Statements.lean) | 36 | B(N) for every N: Newman's theorem, the order, generators, complete presentations, the direct-product criterion, and the errors in the published presentations |
| [2](#part-2) | [`NormalizerDelta/Statements.lean`](NormalizerDelta/Statements.lean) | 34 | Γ_Δ(N): a generalized Newman bound; Γ(N) and X(N); ±Γ₁(N) and X₁(N) (Kim–Koo, Lang) |
| [3](#part-3) | [`NormalizerDelta/StatementsExtra.lean`](NormalizerDelta/StatementsExtra.lean) | 14 | the group M_Δ, finiteness and a coset count for Γ_Δ(N); when h_Δ = h(N); the group B₀(N) |
| [4](#part-4) | [`NormalizerDelta/StatementsXN.lean`](NormalizerDelta/StatementsXN.lean) | 14 | \|SL₂(ℤ/N)\| and the order for X(N); the same group computed in GL₂⁺(ℚ) |
| [5](#part-5) | [`NormalizerDelta/StatementsCartan.lean`](NormalizerDelta/StatementsCartan.lean) | 17 | normalizers of groups of level N; split and non-split Cartan curves |
| [6](#part-6) | [`NormalizerDelta/StatementsGeneral.lean`](NormalizerDelta/StatementsGeneral.lean) | 21 | every Γ ⊇ Γ(N): finiteness with a bound, the local restrictions of Dose–Lido–Mercuri, Nor(Γ_H)/Γ_H ≅ N(H)/H, every group of prime level |
| [7](#part-7) | [`NormalizerDelta/StatementsStar.lean`](NormalizerDelta/StatementsStar.lean) | 20 | Γ_Δ(N) for every Δ: the normalizer exactly (Zemel [Ze]), its order, and when it lies in Nor(Γ₀(N)) |
| [8](#part-8) | [`NormalizerDelta/StatementsMixed.lean`](NormalizerDelta/StatementsMixed.lean) | 18 | Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂) for coprime levels, H₁ as in Part 6 and H₂ arbitrary: the normalizer and its order, with a determinant condition |
| [9](#part-9) | [`NormalizerDelta/StatementsHelling.lean`](NormalizerDelta/StatementsHelling.lean) | 9 | Helling's theorem: every subgroup commensurable with SL₂(ℤ) is conjugate into Γ₀(N)⁺, N squarefree; these are the maximal ones; the commensurator of SL₂(ℤ); normalizers of arithmetic groups |

Highlights:

* **Newman's theorem** [Ne] for every N ≥ 1, in both directions, and the order of B(N) = Nor(Γ₀(N))/Γ₀(N):
  \|B(N)\| = 2^ω(n) ψ(N)/ψ(n). Here h is the largest divisor of 24 with h² ∣ N, n = N/h², and
  ψ(t) = t ∏_{p ∣ t}(1 + 1/p).
* **Complete presentations of B(N) for every N**, which correct the published ones.
  * The Akbaş–Singerman relation [AS] fails in B(256).
  * Bars's presentations [Ba] at levels 32, 64 and 128 define infinite groups.
  * The completed presentations at 32 and 64, and Bars's presentation at 256, present B(32), B(64) and B(256).
  * B(18) ≅ S₄.
* **X₁(N).** For N ≠ 4, Nor(±Γ₁(N)) is generated by Γ₀(N) and the Atkin–Lehner elements [AL] (Kim–Koo [KK], Lang [L]), and
  the modular automorphism group has order 2^ω(N) φ(N)/2. N = 4 is an exception.
* **X(N).** Nor(Γ(N)) = SL₂(ℤ), and the modular automorphism group of X(N) is SL₂(ℤ/N)/{±1}, of order
  N³/2 ∏_{p ∣ N}(1 − 1/p²). For the Klein quartic X(7) this is 168.
* **Every X_Δ(N)** (Zemel [Ze], Cor. 2.6, restated). For every N and every Δ ≤ (ℤ/N)ˣ, let h* be the largest h
  with h² ∣ N, d² ≡ 1 (mod h) for all d ∈ Δ, and Δ ⊇ ker((ℤ/N)ˣ → (ℤ/(N/h))ˣ); put n* = N/h*², D* = diag(h*, 1).
  * Nor(Γ_Δ(N)) = D*⁻¹⟨Γ₀(n*), w_Q : Q ∥ n*, ι_Q(Δ̄) = Δ̄⟩D*, where ι_Q inverts the components of
    (ℤ/(N/h*))ˣ at the primes of Q and Δ̄ is the image of Δ.
  * [Nor(Γ_Δ(N)) : Γ_Δ(N)] = [(ℤ/N)ˣ : Δ] · ψ(N)/ψ(n*) · #{Q ∥ n* : ι_Q(Δ̄) = Δ̄}.
  * Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) iff h* ∣ h(N).
* **Cartan curves.**
  * X_sp(N) ≅ X₀(N²).
  * X_sp(p) (p ≥ 5) and X_ns(p) (p odd) have exactly 2 modular automorphisms.
  * X_sp⁺(p) (p ≥ 7) and X_ns⁺(p) (p ≥ 5) have none, and both bounds on p are sharp.
* **Every congruence subgroup.**
  * Nor(Γ)/Γ is finite, of order at most [SL₂(ℤ) : Γ]·Σ_{D ∣ N} ψ(D).
  * Suppose that, at every p ∣ N, H mod p fixes no line or H mod p^{v_p(N)} lies in a split Cartan subgroup. Then
    Nor(Γ_H)/Γ_H ≅ N(H)/H.
  * At prime level the order is always [N(H) : H], or 2·[N(H) : H] when H fixes exactly one line. In that case
    the Fricke involution supplies the extra automorphisms.
* **Mixed level** (fibre products X_{H₁} ×_{X(1)} X_{H₂}). Let N₁ and N₂ be coprime, let H₁ ≤ SL₂(ℤ/N₁) satisfy the
  hypothesis of the previous item, and let H₂ ≤ SL₂(ℤ/N₂) be arbitrary. Write Det(H₁) for the determinants of the
  normalizer of H₁ in GL₂(ℤ/N₁).
  * Nor(Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂)) ≤ Nor(Γ_{H₂}(N₂)).
  * The order is [N(H₁) : H₁] times the number of classes of Nor(Γ_{H₂})/Γ_{H₂} whose determinant lies in Det(H₁)
    mod N₁. The class of an Atkin–Lehner involution w_Q at level N₂ contains an element of Nor(Γ) iff
    Q mod N₁ ∈ Det(H₁).
  * For Q₈ ≤ SL₂(F₇), Det(Q₈) is the set of squares, so Γ_{Q₈}(7) ∩ Γ₀(3) has order 6, not 6 · 2.
* **Helling's theorem** [He], [Du, Theorem 2.11]. Every subgroup of SL₂(ℝ) commensurable with SL₂(ℤ) is conjugate,
  by (det A)^{-1/2}·A with A integral, into Γ₀(N)⁺ = ⟨Γ₀(N), w_Q : Q ∣ N⟩ for some squarefree N, and for squarefree N
  the group Γ₀(N)⁺ is maximal. So the normalizer of every congruence subgroup is conjugate into some Γ₀(N)⁺, and
  Nor(Γ)/Γ is finite for every Γ commensurable with SL₂(ℤ).

Only **modular** automorphisms are counted, that is, those coming from the normalizer in SL₂(ℝ). Results saying
that every automorphism of a given curve is modular need algebraic geometry that Mathlib does not have, and are
not formalized here.

## Conventions

* **Normalizers are taken in SL₂(ℝ).** For Γ ≤ SL₂(ℤ), `NormG (toR Γ)` is its normalizer in SL₂(ℝ) and
  `BG Γ = NormG Γ ⧸ Γ`; for Γ₀(N) this quotient is `B N`.
  * If −1 ∈ Γ, `BG Γ` is the modular automorphism group of X_Γ (the quotient taken in PSL₂(ℝ)).
  * If −1 ∉ Γ, the curve X_Γ only depends on ±Γ, so its modular automorphism group is `BG (±Γ)`. The order of
    `BG Γ` is twice that of Nor(Γ)/±Γ, which can be smaller than `BG (±Γ)`, because Nor(Γ) ≤ Nor(±Γ) can be strict:
    for Γ₁(4) it is 4, while ±Γ₁(4) = Γ₀(4) gives 6 (`card_BG_GammaDeltaR_4_bot`). For a modular curve one therefore
    uses ±Γ. That is why X(N) appears as ±Γ(N) (`pmGammaR`) and X₁(N) as ±Γ₁(N) (`pmGamma1R`).
* **Rational matrices** enter through `projSL A = (det A)^{−1/2}·A`. Parts 3, 4 and 6 also prove the equivalent
  description: the normalizer in GL₂⁺(ℚ) modulo Γ·ℚ^×.
* **Definitions are honest.** B(N) is defined as the quotient group, not as a presented group. A presentation is
  stated as an isomorphism `PresentedGroup … ≃* B N` that sends each generator to a specified class
  (`IsClassOf`, `IsALClass`), and every other isomorphism is pinned down in the same way.
* Mathlib's `CongruenceSubgroup.Gamma0`, `Gamma1` and `Gamma` are used for Γ₀(N), Γ₁(N) and Γ(N).
* In the presentations, [x, y] = x⁻¹y⁻¹xy, not Mathlib's ⁅x, y⁆.

## How to read the statements

Each part consists of definitions, a statements file `Statements*.lean`, and proof files. The definitions of Parts 1–8
are in one file, [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean), part by part (Part 9 has none); the files
`NormalizerDelta/Defs*.lean` only import it.

* Every theorem in a statements file is proved by one line, `:= by apply X' <;> assumption`, where `X'` is proved
  in the proof files. Lean checks that `X'` gives exactly the stated type.
* So the definitions and statements files are the complete specification. To know what has been proved, you only
  need to read those files, not the proofs.

The tables below paraphrase each statement; each Lean name links to the statement. Part 1 is in the namespace
`NormalizerLean`, and so are Parts 2–6, which import Part 1's definitions.

<a id="part-1"></a>
## Part 1. B(N) = Nor(Γ₀(N))/Γ₀(N)

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 1), [`NormalizerLean/Statements.lean`](NormalizerLean/Statements.lean).

Notation:

* h = h(N) is the largest divisor of 24 with h² ∣ N; n = N/h²; m_p = p^{v_p(N)}.
* w_Q is an Atkin–Lehner element; S_k = [[1, 1/k], [0, 1]].
* Newman's form is ±(1/√e)·[[ae, b/h], [Nc/h, de]] with a, b, c, d ∈ ℤ, e ∣ n and ade² − bcn = e.

| | Lean | statement |
|---|---|---|
| T1 | [`hPart_isGreatest`](NormalizerLean/Statements.lean#L43) | h(N) is the largest divisor of 24 whose square divides N |
| | [`isAtkinLehner_mem_normalizer`](NormalizerLean/Statements.lean#L48) | every Atkin–Lehner element w_Q, Q ∣ N, normalizes Γ₀(N) |
| | [`exists_isAtkinLehner`](NormalizerLean/Statements.lean#L52) | w_Q exists for every Q ∥ N |
| | [`isAtkinLehner_mul_inv_mem`](NormalizerLean/Statements.lean#L57) | two Atkin–Lehner elements for Q differ by an element of Γ₀(N) |
| | [`S_mem_normalizer`](NormalizerLean/Statements.lean#L61) | S_k normalizes Γ₀(N) for every k ∣ h(N) |
| | [`newmanForm_mem_normalizer`](NormalizerLean/Statements.lean#L64) | every matrix of Newman's form normalizes Γ₀(N) |
| T2 | [`newman`](NormalizerLean/Statements.lean#L70) | **Newman's theorem** [Ne]: every element of Nor(Γ₀(N)) has Newman's form |
| T3 | [`Gamma0_index`](NormalizerLean/Statements.lean#L75) | [SL₂(ℤ) : Γ₀(t)] = ψ(t) |
| | [`finite_B`](NormalizerLean/Statements.lean#L79) | B(N) is finite |
| | [`card_B`](NormalizerLean/Statements.lean#L82) | \|B(N)\| = 2^ω(n) ψ(N)/ψ(n) |
| | [`card_B_explicit`](NormalizerLean/Statements.lean#L86) | for N = 2ᵃ3ᵇM, gcd(M, 6) = 1: \|B(N)\| = f₂(a) f₃(b) 2^ω(M), with f₂ = 1, 2, 6, 8, 24, 32, 96, 128 (a = 0, …, 6, ≥ 7) and f₃ = 1, 2, 12, 18 (b = 0, 1, 2, ≥ 3) |
| | [`conjGamma0n_le_normalizer`](NormalizerLean/Statements.lean#L91) | D⁻¹Γ₀(n)D ≤ Nor(Γ₀(N)), D = diag(h, 1) |
| | [`card_CN`](NormalizerLean/Statements.lean#L94) | C(N) = D⁻¹Γ₀(n)D/Γ₀(N) has order ψ(N)/ψ(n) |
| | [`B_mod_CN`](NormalizerLean/Statements.lean#L98) | B(N)/C(N) ≅ (ℤ/2)^ω(n) |
| T4 | [`closure_localGens`](NormalizerLean/Statements.lean#L105) | B(N) is generated by the classes of w_{m_p} and S_{h(m_p)}, p ∣ N |
| T5 | [`localPresentation`](NormalizerLean/Statements.lean#L112) | an explicit presentation of B(pᵃ) for every prime power, with w ↦ w_{pᵃ}, s ↦ S_{h(pᵃ)} |
| T6 | [`localEmbedding`](NormalizerLean/Statements.lean#L120) | B_p = ⟨w_{m_p}, S_{h(m_p)}⟩ ≤ B(N) is isomorphic to B(m_p) via gΓ₀(N) ↦ gΓ₀(m_p) |
| | [`globalPresentation`](NormalizerLean/Statements.lean#L126) | an explicit presentation of B(N) for every N: the local relations, [w_p, w_q] = [s_p, s_q] = 1 and w_p s_q w_p⁻¹ = s_q^{m_p} for p ≠ q |
| T7 | [`internalDirectProduct_iff`](NormalizerLean/Statements.lean#L135) | B(N) is the internal direct product of the B_p iff m_p ≡ 1 mod h(m_q) for all p ≠ q |
| | [`B18_equiv_perm`](NormalizerLean/Statements.lean#L142) | B(18) ≅ S₄ |
| | [`B18_not_C2_prod_A4`](NormalizerLean/Statements.lean#L145) | B(18) ≇ C₂ × A₄ |
| T8 | [`AS_quotient_matrix`](NormalizerLean/Statements.lean#L152) | with w = w₂₅₆ and s = S₈: (ws²ws)(s²wsw)⁻¹ = [[5, −9/8], [−288, 65]] |
| | [`AS_relation_fails`](NormalizerLean/Statements.lean#L157) | the Akbaş–Singerman relation ws²ws = s²wsw fails in B(256) |
| | [`bars_word_matrix`](NormalizerLean/Statements.lean#L162) | wswsws³ws³ = −[[11, 4], [−256, −93]] |
| | [`bars_relation_holds`](NormalizerLean/Statements.lean#L167) | Bars's relation wswsws³ws³ = 1 holds in B(256) |
| | [`bars_lambda5_infinite`](NormalizerLean/Statements.lean#L172) | Bars's presentation at level 32, the triangle group Δ(2, 4, 4), is infinite |
| | [`bars_lambda6_infinite`](NormalizerLean/Statements.lean#L175) | Bars's presentation at level 64, Δ(2, 8, 3), is infinite |
| | [`bars_lambda7_infinite`](NormalizerLean/Statements.lean#L178) | Bars's presentation at level 128, Δ(2, 8, 4), is infinite |
| | [`completed_lambda5_card`](NormalizerLean/Statements.lean#L182) | adding (ws⁻¹ws)² = 1 at level 32 gives a group of order 32 … |
| | [`completed_lambda5`](NormalizerLean/Statements.lean#L187) | … which is B(32), with w ↦ w₃₂, s ↦ S₄ |
| | [`completed_lambda6_card`](NormalizerLean/Statements.lean#L193) | adding (ws⁻¹ws)³ = 1 at level 64 gives order 96 … |
| | [`completed_lambda6`](NormalizerLean/Statements.lean#L198) | … which is B(64), with w ↦ w₆₄, s ↦ S₈ |
| | [`bars_lambda8_card`](NormalizerLean/Statements.lean#L204) | Bars's presentation ⟨w, s \| w², s⁸, wswsws³ws³⟩ at level 256 has order 128 … |
| | [`bars_lambda8`](NormalizerLean/Statements.lean#L210) | … and is a presentation of B(256), with w ↦ w₂₅₆, s ↦ S₈ |
| | [`localRels_mem_Gamma0`](NormalizerLean/Statements.lean#L220) | the local relators hold in B(pᵃ), for every choice of w_{pᵃ} |
| | [`globalRels_mem_Gamma0`](NormalizerLean/Statements.lean#L228) | the global relators hold in B(N), for every choice of the w_{m_p} |

The orders of finitely presented groups (T5, T8) are proved by a coset-enumeration checker written and verified in
Lean ([`CosetCert.lean`](NormalizerLean/CosetCert.lean)), run with `decide +kernel` on the certificates in
[`certs/`](certs). The infinite groups (T8) are proved infinite by explicit actions on ℕ × ℤ in which some
element has infinite order, also checked by `decide` ([`Infinite.lean`](NormalizerLean/Infinite.lean)). The
certificates were generated with Magma and Python. Lean checks them; it does not trust them.

<a id="part-2"></a>
## Part 2. Γ_Δ(N), Γ(N) and ±Γ₁(N)

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 2), [`NormalizerDelta/Statements.lean`](NormalizerDelta/Statements.lean).

Notation:

* Δ ≤ (ℤ/N)ˣ, and Γ_Δ(N) = {[[a, b], [c, d]] ∈ Γ₀(N) : d mod N ∈ Δ}, the group of X_Δ(N).
* i_Δ = [(ℤ/N)ˣ : Δ] and ε_Δ = gcd(N, d² − 1 : d ∈ Δ).
* h_Δ = ∏_p p^{min(v_p(ε_Δ), ⌊v_p(N)/2⌋)} and n_Δ = N/h_Δ².

| | Lean | statement |
|---|---|---|
| Γ_Δ | [`Gamma0R_le_normG_GammaDeltaR`](NormalizerDelta/Statements.lean#L38) | Γ₀(N) normalizes Γ_Δ(N) (the diamond operators) |
| | [`relindex_GammaDelta`](NormalizerDelta/Statements.lean#L43) | [Γ₀(N) : Γ_Δ(N)] = i_Δ |
| | [`GammaDelta_top`](NormalizerDelta/Statements.lean#L47) | Δ = (ℤ/N)ˣ gives Γ₀(N) |
| | [`GammaDelta_pmOne`](NormalizerDelta/Statements.lean#L50) | Δ = {±1} gives ±Γ₁(N) |
| | [`epsDelta_top`](NormalizerDelta/Statements.lean#L54) | for Δ = (ℤ/N)ˣ, ε_Δ = gcd(N, 24) |
| | [`epsDelta_pmOne`](NormalizerDelta/Statements.lean#L57) | for Δ = {±1}, ε_Δ = N |
| | [`hPart_dvd_hDelta`](NormalizerDelta/Statements.lean#L60) | h(N) ∣ h_Δ |
| | [`hDelta_sq_dvd`](NormalizerDelta/Statements.lean#L64) | h_Δ² ∣ N |
| | [`hDelta_top`](NormalizerDelta/Statements.lean#L68) | for Δ = (ℤ/N)ˣ, h_Δ = h(N) |
| | [`isNewmanFormH_hPart_iff`](NormalizerDelta/Statements.lean#L71) | with h = h(N), the form in `newman_delta` is Newman's form |
| | [`newman_delta`](NormalizerDelta/Statements.lean#L79) | **generalized Newman bound:** every element of Nor(Γ_Δ(N)) is ±(1/√e)·[[ae, b/h_Δ], [Nc/h_Δ, de]] with e ∣ n_Δ and ade² − bcn_Δ = e |
| | [`newman_delta_not_sufficient`](NormalizerDelta/Statements.lean#L84) | the converse fails: S₂ has this form for N = 8, Δ = {±1}, but does not normalize ±Γ₁(8) |
| index | [`normG_GammaDeltaR_le_Norm0`](NormalizerDelta/Statements.lean#L90) | if h_Δ = h(N), then Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) |
| | [`S7_mem_normG_GammaDeltaR_49`](NormalizerDelta/Statements.lean#L95) | this fails without h_Δ = h(N): for N = 49 and Δ = {±1 mod 7}, S₇ normalizes Γ_Δ(49) but not Γ₀(49) |
| | [`card_BG_GammaDeltaR`](NormalizerDelta/Statements.lean#L102) | if h_Δ = h(N): [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ·s_Δ, where s_Δ is the number of elements of B(N) normalizing Γ_Δ(N) |
| | [`sDelta_eq_sIota`](NormalizerDelta/Statements.lean#L110) | if 4 ∤ N and 9 ∤ N: s_Δ = #{Q ∥ N : ι_Q(Δ) = Δ}, where ι_Q(d) ≡ d⁻¹ mod Q and ι_Q(d) ≡ d mod N/Q |
| | [`card_BG_GammaDeltaR_of_not_dvd`](NormalizerDelta/Statements.lean#L115) | the two combined: [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ·#{Q ∥ N : ι_Q(Δ) = Δ} |
| Γ(N) | [`normG_GammaR`](NormalizerDelta/Statements.lean#L122) | Nor(Γ(N)) = SL₂(ℤ), for every N ≥ 1 |
| | [`normG_pmGammaR`](NormalizerDelta/Statements.lean#L125) | Nor(±Γ(N)) = SL₂(ℤ) |
| | [`BG_GammaR_equiv`](NormalizerDelta/Statements.lean#L129) | Nor(Γ(N))/Γ(N) ≅ SL₂(ℤ/N), γ ↦ γ mod N |
| | [`BG_pmGammaR_equiv`](NormalizerDelta/Statements.lean#L136) | **the modular automorphism group of X(N)**: Nor(±Γ(N))/±Γ(N) ≅ SL₂(ℤ/N)/{±1} |
| | [`conj_GammaDelta_sq`](NormalizerDelta/Statements.lean#L145) | for Δ = {±1 mod M}, conjugation by diag(M, 1) maps Γ_Δ(M²) onto ±Γ(M), so X_Δ(M²) ≅ X(M) |
| | [`conj_GammaDelta_X1MN`](NormalizerDelta/Statements.lean#L152) | if M² ∣ N and Δ = {±1 mod N/M}, conjugation by diag(M, 1) maps Γ_Δ(N) onto ±(Γ(M) ∩ Γ₁(N/M)), so X_Δ(N) ≅ X₁(M, N/M) |
| ±Γ₁(N) | [`Gamma0R_le_normG_pmGamma1R`](NormalizerDelta/Statements.lean#L162) | Γ₀(N) normalizes ±Γ₁(N) |
| | [`isAtkinLehner_mem_normG_pmGamma1R`](NormalizerDelta/Statements.lean#L166) | every w_Q, Q ∣ N, normalizes ±Γ₁(N) |
| | [`normG_pmGamma1R`](NormalizerDelta/Statements.lean#L173) | **Kim–Koo [KK], Lang [L]:** for N ≠ 4, g normalizes ±Γ₁(N) iff g is an Atkin–Lehner element w_Q for some Q ∥ N |
| | [`isAtkinLehner_one_iff`](NormalizerDelta/Statements.lean#L178) | the Atkin–Lehner elements for Q = 1 are exactly Γ₀(N) |
| | [`pmGamma1R_four`](NormalizerDelta/Statements.lean#L181) | the exception N = 4: ±Γ₁(4) = Γ₀(4) |
| | [`S2_mem_normG_pmGamma1R_four`](NormalizerDelta/Statements.lean#L185) | S₂ normalizes ±Γ₁(4) but is not an Atkin–Lehner element |
| | [`card_BG_pmGamma1R_four`](NormalizerDelta/Statements.lean#L189) | \|Nor(±Γ₁(4))/±Γ₁(4)\| = \|B(4)\| = 6 |
| | [`card_BG_pmGamma1R`](NormalizerDelta/Statements.lean#L194) | **the order for X₁(N)**: \|Nor(±Γ₁(N))/±Γ₁(N)\| = 2^ω(N) φ(N)/2 for N ≥ 3, N ≠ 4 |
| | [`diamonds_normal`](NormalizerDelta/Statements.lean#L199) | the diamond subgroup is normal |
| | [`card_diamonds`](NormalizerDelta/Statements.lean#L202) | the diamond subgroup has order φ(N)/2 (N ≥ 3) |
| | [`BG_pmGamma1R_mod_diamonds`](NormalizerDelta/Statements.lean#L207) | for N ≠ 4 the quotient by the diamonds is (ℤ/2)^ω(N), with w_Q ↦ the primes dividing Q |

<a id="part-3"></a>
## Part 3. More on Γ_Δ(N), and B₀(N)

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 3), [`NormalizerDelta/StatementsExtra.lean`](NormalizerDelta/StatementsExtra.lean).

| | Lean | statement |
|---|---|---|
| M_Δ | [`coe_MDelta`](NormalizerDelta/StatementsExtra.lean#L36) | the matrices of the generalized Newman bound form the group M_Δ = D⁻¹Γ₀(n_Δ)⁺D, D = diag(h_Δ, 1) |
| | [`Gamma0R_le_MDelta`](NormalizerDelta/StatementsExtra.lean#L40) | Γ₀(N) ≤ M_Δ |
| | [`relIndex_Gamma0R_MDelta_ne_zero`](NormalizerDelta/StatementsExtra.lean#L43) | [M_Δ : Γ₀(N)] is finite |
| | [`normG_GammaDeltaR_le_MDelta`](NormalizerDelta/StatementsExtra.lean#L47) | Nor(Γ_Δ(N)) ≤ M_Δ |
| | [`finite_BG_GammaDeltaR`](NormalizerDelta/StatementsExtra.lean#L51) | Nor(Γ_Δ(N))/Γ_Δ(N) is finite, for every Δ |
| | [`card_BG_GammaDeltaR_eq`](NormalizerDelta/StatementsExtra.lean#L58) | [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ·[Nor(Γ_Δ(N)) : Γ₀(N)] |
| | [`exists_sigmaH`](NormalizerDelta/StatementsExtra.lean#L64) | every coset Γ₀(N)g in M_Δ contains a real multiple of σH, with σ from a fixed set of representatives of Γ₀(N)\SL₂(ℤ) and H = [[a, b], [0, d]] a Hermite form (ad ∣ N, 0 ≤ b < d, gcd(a, b, d) = 1) |
| | [`sigmaH_unique`](NormalizerDelta/StatementsExtra.lean#L72) | the pair (σ, H) is unique |
| | [`exists_Gamma0Reps`](NormalizerDelta/StatementsExtra.lean#L81) | sets of representatives of Γ₀(N)\SL₂(ℤ) exist |
| | [`relIndex_normG_eq_card_sigmaH`](NormalizerDelta/StatementsExtra.lean#L86) | [Nor(Γ_Δ(N)) : Γ₀(N)] is the number of pairs (σ, H) such that σH normalizes Γ_Δ(N); this is the count computed by [`scripts/aut_orders.py`](scripts/aut_orders.py) |
| h_Δ | [`hDelta_eq_hPart_iff`](NormalizerDelta/StatementsExtra.lean#L97) | h_Δ = h(N) iff none of the following holds: (i) p² ∣ N and Δ ⊆ {±1 mod p} for some prime p ≥ 5; (ii) 3⁴ ∣ N and Δ ⊆ {±1 mod 9}; (iii) 2⁸ ∣ N and Δ ⊆ {±1 mod 8} |
| B₀(N) | [`mem_center_GLPos_iff`](NormalizerDelta/StatementsExtra.lean#L106) | the centre of GL₂⁺(ℚ) consists of the nonzero scalar matrices |
| | [`B0_equiv`](NormalizerDelta/StatementsExtra.lean#L113) | the group B₀(N) of [DN]: g ↦ (det g)^{−1/2}·g induces Nor_{GL₂⁺(ℚ)}(Γ₀(N))/(Γ₀(N)·ℚ^×) ≅ B(N) |
| | [`infinite_B0lit`](NormalizerDelta/StatementsExtra.lean#L120) | without the scalars, Nor_{GL₂⁺(ℚ)}(Γ₀(N))/Γ₀(N) is infinite |

<a id="part-4"></a>
## Part 4. The order for X(N)

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 4), [`NormalizerDelta/StatementsXN.lean`](NormalizerDelta/StatementsXN.lean).

| | Lean | statement |
|---|---|---|
| order | [`relIndex_Gamma1_Gamma0`](NormalizerDelta/StatementsXN.lean#L38) | [Γ₀(N) : Γ₁(N)] = φ(N) |
| | [`relIndex_Gamma_Gamma1`](NormalizerDelta/StatementsXN.lean#L42) | [Γ₁(N) : Γ(N)] = N |
| | [`index_Gamma`](NormalizerDelta/StatementsXN.lean#L46) | [SL₂(ℤ) : Γ(N)] = N³ ∏_{p ∣ N}(1 − 1/p²) |
| | [`card_SL2_ZMod`](NormalizerDelta/StatementsXN.lean#L50) | \|SL₂(ℤ/N)\| = N³ ∏_{p ∣ N}(1 − 1/p²) |
| | [`card_BG_GammaR`](NormalizerDelta/StatementsXN.lean#L54) | [Nor(Γ(N)) : Γ(N)] = \|SL₂(ℤ/N)\| |
| | [`card_PSL2_ZMod`](NormalizerDelta/StatementsXN.lean#L58) | \|SL₂(ℤ/N)/{±1}\| = N³/2 ∏_{p ∣ N}(1 − 1/p²) for N ≥ 3 |
| | [`card_BG_pmGammaR`](NormalizerDelta/StatementsXN.lean#L64) | **X(N) has N³/2 ∏_{p ∣ N}(1 − 1/p²) modular automorphisms**, for N ≥ 3 |
| | [`card_BG_pmGammaR_le_two`](NormalizerDelta/StatementsXN.lean#L68) | for N ≤ 2 there is no factor 1/2: the order is 1 (N = 1) or 6 (N = 2) |
| | [`card_BG_pmGammaR_seven`](NormalizerDelta/StatementsXN.lean#L72) | X(7), the Klein quartic: 168 |
| | [`card_BG_GammaDeltaR_sq`](NormalizerDelta/StatementsXN.lean#L80) | for M ≥ 3 and Δ = {±1 mod M}: [Nor(Γ_Δ(M²)) : Γ_Δ(M²)] = M³/2 ∏_{p ∣ M}(1 − 1/p²) |
| | [`card_BG_GammaDeltaR_49`](NormalizerDelta/StatementsXN.lean#L85) | X_Δ(49), Δ = {±1 mod 7}: 168 |
| GL₂⁺(ℚ) | [`normGQ_GammaQ`](NormalizerDelta/StatementsXN.lean#L91) | the normalizer of Γ(N) in GL₂⁺(ℚ) is SL₂(ℤ)·ℚ^× |
| | [`BQ_GammaQ_equiv_BG`](NormalizerDelta/StatementsXN.lean#L97) | Nor_{GL₂⁺(ℚ)}(Γ(N))/(Γ(N)·ℚ^×) ≅ Nor(±Γ(N))/±Γ(N) |
| | [`BQ_GammaQ_equiv`](NormalizerDelta/StatementsXN.lean#L105) | Nor_{GL₂⁺(ℚ)}(Γ(N))/(Γ(N)·ℚ^×) ≅ SL₂(ℤ/N)/{±1} |

<a id="part-5"></a>
## Part 5. Cartan modular curves

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 5), [`NormalizerDelta/StatementsCartan.lean`](NormalizerDelta/StatementsCartan.lean).

The groups are defined by congruences in SL₂(ℤ):

* Γ_sp(N): γ ≡ diagonal mod N. Γ_sp⁺(N): γ ≡ diagonal or antidiagonal mod N.
* Γ_ns(p): γ ≡ [[a, εc], [c, a]] mod p, with ε a non-square mod p. Γ_ns⁺(p) also allows [[a, −εc], [c, −a]].

| | Lean | statement |
|---|---|---|
| level N | [`normG_level_form`](NormalizerDelta/StatementsCartan.lean#L45) | [DLM26, Prop. 4.3(2)]: if Γ(N) ≤ Γ, every element of Nor(Γ) is (det m)^{−1/2}·m for an integral m with no prime dividing all its entries and 0 < det m ∣ N |
| | [`normG_level_le_SL2ZR`](NormalizerDelta/StatementsCartan.lean#L54) | [DLM26, Prop. 4.5(1)]: if, for every p ∣ N, Γ mod p fixes no line of F_p², then Nor(Γ) ≤ SL₂(ℤ) |
| split | [`index_GammaSp`](NormalizerDelta/StatementsCartan.lean#L63) | [SL₂(ℤ) : Γ_sp(N)] = N² ∏_{p ∣ N}(1 + 1/p) |
| | [`conj_GammaSp`](NormalizerDelta/StatementsCartan.lean#L68) | X_sp(N) ≅ X₀(N²): conjugation by diag(N, 1)⁻¹ maps Γ_sp(N) onto Γ₀(N²) |
| | [`card_BG_GammaSp`](NormalizerDelta/StatementsCartan.lean#L74) | \|Nor(Γ_sp(N))/Γ_sp(N)\| = \|B(N²)\| |
| | [`card_BG_GammaSp_two_three`](NormalizerDelta/StatementsCartan.lean#L78) | X_sp(2) and X_sp(3) have 6 and 12 modular automorphisms |
| | [`normG_GammaSp`](NormalizerDelta/StatementsCartan.lean#L82) | for primes p ≥ 5, Nor(Γ_sp(p)) = Γ_sp⁺(p) |
| | [`card_BG_GammaSp_prime`](NormalizerDelta/StatementsCartan.lean#L86) | for primes p ≥ 5, X_sp(p) has exactly 2 modular automorphisms |
| | [`normG_GammaSpPlus`](NormalizerDelta/StatementsCartan.lean#L90) | for primes p ≥ 7, Γ_sp⁺(p) is its own normalizer |
| | [`card_BG_GammaSpPlus`](NormalizerDelta/StatementsCartan.lean#L94) | for primes p ≥ 7, X_sp⁺(p) has no non-trivial modular automorphisms |
| | [`GammaSpPlus_five_lt`](NormalizerDelta/StatementsCartan.lean#L99) | p ≥ 7 is needed: Γ_sp⁺(5) is not its own normalizer |
| non-split | [`index_GammaNs`](NormalizerDelta/StatementsCartan.lean#L104) | for odd primes p, [SL₂(ℤ) : Γ_ns(p)] = p(p − 1) |
| | [`normG_GammaNs`](NormalizerDelta/StatementsCartan.lean#L108) | for odd primes p, Nor(Γ_ns(p)) = Γ_ns⁺(p) |
| | [`card_BG_GammaNs`](NormalizerDelta/StatementsCartan.lean#L112) | for odd primes p, X_ns(p) has exactly 2 modular automorphisms |
| | [`normG_GammaNsPlus`](NormalizerDelta/StatementsCartan.lean#L116) | for primes p ≥ 5, Γ_ns⁺(p) is its own normalizer |
| | [`card_BG_GammaNsPlus`](NormalizerDelta/StatementsCartan.lean#L120) | for primes p ≥ 5, X_ns⁺(p) has no non-trivial modular automorphisms |
| | [`GammaNsPlus_three_lt`](NormalizerDelta/StatementsCartan.lean#L125) | p ≥ 5 is needed: Γ_ns⁺(3) is not its own normalizer |

<a id="part-6"></a>
## Part 6. General modular curves X_H

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 6), [`NormalizerDelta/StatementsGeneral.lean`](NormalizerDelta/StatementsGeneral.lean).
Proposition numbers refer to [DLM26].

Notation and the −1 convention:

* H ≤ SL₂(ℤ/N), Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H}, and N(H) is the normalizer of H in SL₂(ℤ/N).
* "H mod q lies in a Borel / split Cartan subgroup" means that it fixes one line / two independent lines of
  (ℤ/q)². W_p = (1/√p)·[[0, −1], [p, 0]] is the Fricke involution.
* If −1 ∉ H, the modular automorphism group of X_H is the one of H·{±1}. The hypotheses below hold for H iff they
  hold for H·{±1}.

| | Lean | statement |
|---|---|---|
| Γ_H | [`GammaH_map`](NormalizerDelta/StatementsGeneral.lean#L56) | every Γ ⊇ Γ(N) is Γ_H, with H = Γ mod N |
| | [`index_GammaH`](NormalizerDelta/StatementsGeneral.lean#L60) | [SL₂(ℤ) : Γ_H] = [SL₂(ℤ/N) : H] |
| SL₂(ℤ) part | [`ofZ_mem_normG_GammaH_iff`](NormalizerDelta/StatementsGeneral.lean#L65) | [Algorithm 4.9, Step 3]: γ ∈ SL₂(ℤ) normalizes Γ_H iff γ mod N normalizes H |
| | [`normG_GammaH_inf_SL2ZR`](NormalizerDelta/StatementsGeneral.lean#L69) | Nor(Γ_H) ∩ SL₂(ℤ) = Γ_{N(H)} |
| | [`relIndex_normG_inf_SL2ZR`](NormalizerDelta/StatementsGeneral.lean#L74) | [Nor(Γ_H) ∩ SL₂(ℤ) : Γ_H] = [N(H) : H] |
| finiteness | [`projSL_inv_mul_mem_GammaR`](NormalizerDelta/StatementsGeneral.lean#L82) | [Prop. 4.3(4)]: integral m, m′ of the same determinant D with m ≡ m′ mod N·D give the same coset of Γ(N) |
| | [`mem_normG_iff_of_reps`](NormalizerDelta/StatementsGeneral.lean#L89) | [Prop. 4.3(3)]: a finite test. If S ⊆ Γ represents Γ mod N², then m (0 < det m ∣ N) normalizes Γ iff msm⁻¹ ∈ Γ and m⁻¹sm ∈ Γ for all s ∈ S |
| | [`finite_BG`](NormalizerDelta/StatementsGeneral.lean#L99) | Nor(Γ)/Γ is finite for every Γ ⊇ Γ(N) |
| | [`card_BG_le`](NormalizerDelta/StatementsGeneral.lean#L105) | \|Nor(Γ)/Γ\| ≤ [SL₂(ℤ) : Γ]·Σ_{D ∣ N} ψ(D) (not stated in [DLM26]) |
| local | [`isBorelMod_of_dvd_det`](NormalizerDelta/StatementsGeneral.lean#L115) | [Prop. 4.5(1)]: if (det m)^{−1/2}·m normalizes Γ_H, p does not divide all entries of m, and p^k ∣ det m, then H mod p^k lies in a Borel subgroup |
| | [`borel_shape`](NormalizerDelta/StatementsGeneral.lean#L122) | [Prop. 4.5(2)]: if moreover H mod p lies in the standard Borel subgroup but not in a split Cartan subgroup, and p ∣ det m, then m ≡ [[0, ∗], [0, 0]] mod p |
| | [`le_of_isSplitMod`](NormalizerDelta/StatementsGeneral.lean#L130) | [Prop. 4.5(4)]: if p^k ∣ N and H mod p^k lies in a split Cartan subgroup, then v_p(det m) ≤ v_p(N) − k |
| general theorem | [`normG_GammaH`](NormalizerDelta/StatementsGeneral.lean#L141) | if, for every p ∣ N, H mod p fixes no line or H mod p^{v_p(N)} lies in a split Cartan subgroup, then Nor(Γ_H) = Γ_{N(H)} |
| | [`BG_GammaH_equiv`](NormalizerDelta/StatementsGeneral.lean#L148) | under the same hypothesis, **Nor(Γ_H)/Γ_H ≅ N(H)/H**, with γ ↦ γ mod N |
| | [`card_BG_GammaH`](NormalizerDelta/StatementsGeneral.lean#L156) | under the same hypothesis, \|Nor(Γ_H)/Γ_H\| = [N(H) : H] |
| prime level | [`fixesUniqueLine_iff`](NormalizerDelta/StatementsGeneral.lean#L164) | if H ≤ SL₂(F_p) fixes the line through (1, 0), that line is the only one fixed by H iff Γ₁(p) ≤ Γ_H |
| | [`card_BG_GammaH_prime`](NormalizerDelta/StatementsGeneral.lean#L169) | if H fixes no line or at least two lines of F_p², then \|Nor(Γ_H)/Γ_H\| = [N(H) : H] |
| | [`card_BG_GammaH_prime_unique`](NormalizerDelta/StatementsGeneral.lean#L174) | if H fixes exactly one line, then \|Nor(Γ_H)/Γ_H\| = 2·[N(H) : H] |
| | [`normG_GammaH_prime_unique`](NormalizerDelta/StatementsGeneral.lean#L180) | in that case, with the line moved to the line through (1, 0): Nor(Γ_H) = ⟨Γ_{N(H)}, W_p⟩ |
| GL₂⁺(ℚ) | [`BQ_equiv_BG`](NormalizerDelta/StatementsGeneral.lean#L189) | [(4.1), Prop. 4.3(1)]: for Γ ⊇ Γ(N) with −1 ∈ Γ, Nor_{GL₂⁺(ℚ)}(Γ)/(Γ·ℚ^×) ≅ Nor(Γ)/Γ |
| sanity | [`card_BG_GammaH_pmOne`](NormalizerDelta/StatementsGeneral.lean#L200) | for H = {±1}: 25308, 20520 and 26208 at N = 37, 38, 39, the orders in [DLM26, Table 3] |

The general theorem and the prime-level results are not stated in [DLM26]. They follow from its Section 4.1; the
case of Cartan groups is [DLM22, Prop. 5.6].

<a id="part-7"></a>
## Part 7. The normalizer of Γ_Δ(N) for every Δ

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 7), [`NormalizerDelta/StatementsStar.lean`](NormalizerDelta/StatementsStar.lean).

This part determines Nor(Γ_Δ(N)) for every N and every subgroup Δ ≤ (ℤ/N)ˣ, with or without −1. The result is
Zemel's [Ze, Cor. 2.6] (with Lemma 2.4, Prop. 2.7 and Prop. 1.9(iii) there), restated in closed form: h* is his
σ_H, and D*⁻¹Γ₀(n*)⁺D* is his Γ₀^{∗,σ_H}(N). The order formula is not stated there in this form, but it follows
directly.

Notation:

* C(h) (`IsHStar`): h² ∣ N, d² ≡ 1 (mod h) for every d ∈ Δ, and Δ contains every unit u ≡ 1 (mod N/h).
* h* (`hStar`) is the largest h with C(h). Then n* = N/h*² (`nStar`) and D* = diag(h*, 1) (`Dstar`).
* For Q ∥ n*, ι*_Q inverts the components of (ℤ/(N/h*))ˣ at the primes of Q (`IsIotaStar`). Δ̄ is the image of Δ
  in (ℤ/(N/h*))ˣ, and w* = #{Q ∥ n* : ι*_Q(Δ̄) = Δ̄} (`wStar`).

| | Lean | statement |
|---|---|---|
| h* | [`isHStar_one`](NormalizerDelta/StatementsStar.lean#L44) | h = 1 satisfies C(h) |
|  | [`isHStar_hStar`](NormalizerDelta/StatementsStar.lean#L47) | h* satisfies C(h) |
|  | [`dvd_hStar`](NormalizerDelta/StatementsStar.lean#L50) | every h with C(h) divides h* |
|  | [`hStar_dvd_hDelta`](NormalizerDelta/StatementsStar.lean#L54) | h* ∣ h_Δ |
|  | [`hStar_top`](NormalizerDelta/StatementsStar.lean#L57) | for Γ₀(N): h* = h(N) |
|  | [`hStar_pmOne`](NormalizerDelta/StatementsStar.lean#L60) | for ±Γ₁(N), N ≠ 4: h* = 1 |
|  | [`hStar_pmOne_four`](NormalizerDelta/StatementsStar.lean#L63) | for ±Γ₁(4) = Γ₀(4): h* = 2 |
|  | [`hStar_deltaPm_sq`](NormalizerDelta/StatementsStar.lean#L66) | for N = M² and Δ = {±1 mod M} (X_Δ(M²) ≅ X(M)): h* = M |
| bounds | [`Gamma0Star_le_normG`](NormalizerDelta/StatementsStar.lean#L72) | D*⁻¹Γ₀(n*)D* ≤ Nor(Γ_Δ(N)) |
|  | [`Gamma0R_le_Gamma0Star`](NormalizerDelta/StatementsStar.lean#L76) | Γ₀(N) ≤ D*⁻¹Γ₀(n*)D*, of index ψ(N)/ψ(n*) |
|  | [`normG_le_MStar`](NormalizerDelta/StatementsStar.lean#L81) | **the sharp generalized Newman bound**: Nor(Γ_Δ(N)) ≤ D*⁻¹Γ₀(n*)⁺D* |
|  | [`MStar_le_MDelta`](NormalizerDelta/StatementsStar.lean#L85) | D*⁻¹Γ₀(n*)⁺D* ≤ M_Δ, so this sharpens Part 3 |
| Atkin–Lehner | [`isIotaStable_one`](NormalizerDelta/StatementsStar.lean#L88) | Q = 1 always satisfies ι*_Q(Δ̄) = Δ̄ |
|  | [`conj_mem_normG_iff`](NormalizerDelta/StatementsStar.lean#L92) | for an Atkin–Lehner element w of level n* for Q ∥ n*: D*⁻¹wD* normalizes Γ_Δ(N) iff ι*_Q(Δ̄) = Δ̄ |
| the normalizer | [`mem_normG_GammaDeltaR_iff`](NormalizerDelta/StatementsStar.lean#L98) | **Nor(Γ_Δ(N)) = D*⁻¹⟨Γ₀(n*), w_Q : Q ∥ n*, ι*_Q(Δ̄) = Δ̄⟩D***: g normalizes Γ_Δ(N) iff D*gD*⁻¹ is an Atkin–Lehner element of level n* for such a Q |
|  | [`card_BG_GammaDeltaR_hStar`](NormalizerDelta/StatementsStar.lean#L106) | **the order**: [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ · ψ(N)/ψ(n*) · w*, for every N and Δ |
|  | [`wStar_eq_sIota`](NormalizerDelta/StatementsStar.lean#L111) | if h* = 1, then w* = #{Q ∥ N : ι_Q(Δ) = Δ}, Part 2's count, with no condition on 4 ∣ N or 9 ∣ N |
|  | [`normG_GammaDeltaR_le_Norm0_iff`](NormalizerDelta/StatementsStar.lean#L115) | Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) iff h* ∣ h(N) |
| sanity | [`card_BG_GammaDeltaR_50`](NormalizerDelta/StatementsStar.lean#L120) | X_Δ(50), Δ = {±1 mod 5} (Bring's curve): 120 = 2 · 90/3 · 2 |
|  | [`card_BG_GammaDeltaR_4_bot`](NormalizerDelta/StatementsStar.lean#L126) | Γ₁(4) (Δ = {1}): 4 = 2 · 1 · 2, while ±Γ₁(4) = Γ₀(4) gives 6 |

Special cases:

* Δ = (ℤ/N)ˣ gives Newman's theorem and \|B(N)\| (Part 1).
* Δ = {±1} with N ≠ 4 gives Kim–Koo and Lang (Part 2).
* N = M² and Δ = {±1 mod M} give the order for X(M) (Part 4).

<a id="part-8"></a>
## Part 8. Mixed level: Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂)

Files: [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) (Part 8), [`NormalizerDelta/StatementsMixed.lean`](NormalizerDelta/StatementsMixed.lean).

N₁ and N₂ are coprime, H₁ ≤ SL₂(ℤ/N₁) and H₂ ≤ SL₂(ℤ/N₂), and Γ = Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂) = Γ_{H₁ × H₂}, the
group of the fibre product X_{H₁} ×_{X(1)} X_{H₂}.

* "H₁ of type I" is the hypothesis of Part 6's general theorem at level N₁: for every p ∣ N₁, H₁ mod p fixes no
  line, or H₁ mod p^{v_p(N₁)} lies in a split Cartan subgroup. H₂ is arbitrary, for example Γ_Δ(N₂) of Part 7 or a
  group of prime level with one fixed line.
* Det(H₁) (`IsNormDet`) is the set of determinants of the normalizer of H₁ in GL₂(ℤ/N₁) (`NormalizesMat`). It
  contains the squares.
* An element of Nor is x = (det m)^{-1/2}·m with m integral, and `HasNormDet` says that det m mod N₁ is a unit in
  Det(H₁).

| | Lean | statement |
|---|---|---|
| structure | [`isUnit_det_of_mem_normG_inf`](NormalizerDelta/StatementsMixed.lean#L59) | for H₁ of type I, every x ∈ Nor(Γ) has det m prime to N₁ |
|  | [`normG_inf_le`](NormalizerDelta/StatementsMixed.lean#L68) | for H₁ of type I, Nor(Γ) ≤ Nor(Γ_{H₂}(N₂)) |
|  | [`mem_normG_inf_iff`](NormalizerDelta/StatementsMixed.lean#L75) | for every H₁: x ∈ Nor(Γ_{H₂}(N₂)), det m prime to N₁, normalizes Γ iff m mod N₁ normalizes H₁ |
|  | [`normG_inf_inf_eq`](NormalizerDelta/StatementsMixed.lean#L83) | Nor(Γ) ∩ Γ_{H₂}(N₂) = Γ_{N(H₁)}(N₁) ∩ Γ_{H₂}(N₂) |
|  | [`relIndex_inf_normG`](NormalizerDelta/StatementsMixed.lean#L89) | [Nor(Γ) ∩ Γ_{H₂}(N₂) : Γ] = [N(H₁) : H₁] |
|  | [`exists_mul_mem_normG_inf_iff`](NormalizerDelta/StatementsMixed.lean#L97) | the class x·Γ_{H₂}(N₂) meets Nor(Γ) iff det m mod N₁ ∈ Det(H₁); the ⇐ is the lifting of Box [Bo, Lemma 2.7] |
| the order | [`card_BG_inf`](NormalizerDelta/StatementsMixed.lean#L109) | **\|Nor(Γ)/Γ\| = [N(H₁) : H₁] · #{classes of Nor(Γ_{H₂})/Γ_{H₂} with det m mod N₁ ∈ Det(H₁)}**, for H₁ of type I and every H₂ |
|  | [`card_BG_inf_of_isNormDet`](NormalizerDelta/StatementsMixed.lean#L117) | if Det(H₁) = (ℤ/N₁)ˣ: \|Nor(Γ)/Γ\| = [N(H₁) : H₁] · \|Nor(Γ_{H₂})/Γ_{H₂}\| |
|  | [`card_BG_inf_GammaDelta`](NormalizerDelta/StatementsMixed.lean#L127) | for Γ_Δ(N₂): [N(H₁) : H₁] · i_Δ · ψ(N₂)/ψ(n*) · #{Q ∥ n* : ι*_Q(Δ̄) = Δ̄, Q mod N₁ ∈ Det(H₁)} (Part 7 is N₁ = 1) |
|  | [`card_BG_inf_prime_unique`](NormalizerDelta/StatementsMixed.lean#L136) | for H₂ of prime level p with exactly one fixed line, p mod N₁ ∈ Det(H₁): 2 · [N(H₁) : H₁] · [N(H₂) : H₂] |
|  | [`card_BG_inf_prime_unique_of_not`](NormalizerDelta/StatementsMixed.lean#L145) | the same with p mod N₁ ∉ Det(H₁): [N(H₁) : H₁] · [N(H₂) : H₂] (no element of the class of the Fricke involution normalizes Γ) |
| corollaries | [`card_BG_Gamma_inf`](NormalizerDelta/StatementsMixed.lean#L154) | Γ(N₁) ∩ Γ_{H₂}(N₂): \|SL₂(ℤ/N₁)\| · \|Nor(Γ_{H₂})/Γ_{H₂}\| (in SL₂(ℝ); −1 ∉ Γ(N₁) for N₁ ≥ 3, so this is not the count for X(N₁) ×_{X(1)} X_{H₂}) |
|  | [`card_BG_GammaNsPlus_inf`](NormalizerDelta/StatementsMixed.lean#L160) | Γ_ns⁺(p) ∩ Γ_{H₂}(N₂), p ≥ 5: as many as Γ_{H₂}(N₂) |
|  | [`card_BG_GammaSpPlus_inf`](NormalizerDelta/StatementsMixed.lean#L165) | Γ_sp⁺(p) ∩ Γ_{H₂}(N₂), p ≥ 7: as many as Γ_{H₂}(N₂) |
| sanity | [`isNormDet_Q8mod7_iff`](NormalizerDelta/StatementsMixed.lean#L172) | for Q₈ ≤ SL₂(F₇), Det(Q₈) is the set of non-zero squares |
|  | [`card_BG_Q8mod7`](NormalizerDelta/StatementsMixed.lean#L175) | \|Nor(Γ_{Q₈}(7))/Γ_{Q₈}(7)\| = 6 |
|  | [`card_BG_Q8mod7_inf_two`](NormalizerDelta/StatementsMixed.lean#L178) | Γ_{Q₈}(7) ∩ Γ₀(2): 12 = 6 · 2, as 2 = 3² mod 7 |
|  | [`card_BG_Q8mod7_inf_three`](NormalizerDelta/StatementsMixed.lean#L182) | Γ_{Q₈}(7) ∩ Γ₀(3): 6, not 6 · 2, as 3 is not a square mod 7 |

Sources: the restriction det m prime to N₁ is [DLM26, Prop. 4.5(1), (4)], as in Part 6. The lifting in
`exists_mul_mem_normG_inf_iff` (⇐) is [Bo, Lemma 2.7]. [DLM22, Prop. 5.6] is the case of Cartan groups and
N₂ = 2. The other statements were not found in this form in the literature checked (October 2026, not exhaustive).

The statements are about orders: §A gives an extension 1 → N(H₁)/H₁ → Nor(Γ)/Γ → {classes with det m mod N₁ ∈
Det(H₁)} → 1, not a product, and "w_Q survives" in the docstrings means that the class of w_Q contains an element of
Nor(Γ) (W₂ itself does not normalize Γ_{Q₈}(7) ∩ Γ₀(2), but another element of its class does). After freezing, the
statements were reviewed by two AI reviewer agents (blind and adversarial), who found no statement whose meaning
differs from its description.

<a id="part-9"></a>
## Part 9. Helling's theorem

Files: [`NormalizerDelta/StatementsHelling.lean`](NormalizerDelta/StatementsHelling.lean). Part 9 has no new
definitions. Its formalization was suggested by Maarten Derickx.

A subgroup G ≤ SL₂(ℝ) is commensurable with SL₂(ℤ) if G ∩ SL₂(ℤ) has finite index in G and in SL₂(ℤ) (Mathlib's
`Subgroup.Commensurable G SL2ZR`). Γ₀(N)⁺ = ⟨w_Q : Q ∣ N⟩ is `Gamma0Plus N` of Part 3. For an integral matrix A with
det A > 0, `projSL A` = (det A)^{-1/2}·A ∈ SL₂(ℝ).

| | Lean | statement |
|---|---|---|
| Helling | [`helling`](NormalizerDelta/StatementsHelling.lean#L47) | **every G commensurable with SL₂(ℤ) is conjugate into Γ₀(N)⁺ for some squarefree N**, by (det A)^{-1/2}·A with A integral, det A > 0 |
|  | [`commensurable_gamma0Plus`](NormalizerDelta/StatementsHelling.lean#L52) | Γ₀(N)⁺ is commensurable with SL₂(ℤ), for every N ≥ 1 |
|  | [`gamma0Plus_maximal`](NormalizerDelta/StatementsHelling.lean#L55) | for squarefree N, every H ⊇ Γ₀(N)⁺ commensurable with SL₂(ℤ) is Γ₀(N)⁺ |
|  | [`maximal_commensurable_iff`](NormalizerDelta/StatementsHelling.lean#L61) | the maximal subgroups commensurable with SL₂(ℤ) are the conjugates of the Γ₀(N)⁺, N squarefree, that are commensurable with SL₂(ℤ) [Du, Theorem 2.11] |
|  | [`mem_commensurator_SL2ZR_iff`](NormalizerDelta/StatementsHelling.lean#L68) | the commensurator of SL₂(ℤ) in SL₂(ℝ) is {(det A)^{-1/2}·A : A integral, det A > 0} |
| normalizers | [`commensurable_normG`](NormalizerDelta/StatementsHelling.lean#L75) | for Γ commensurable with SL₂(ℤ), so is Nor(Γ) |
|  | [`finite_BG_of_commensurable`](NormalizerDelta/StatementsHelling.lean#L79) | for Γ commensurable with SL₂(ℤ), Nor(Γ)/Γ is finite |
|  | [`normG_conj_le_gamma0Plus`](NormalizerDelta/StatementsHelling.lean#L83) | for Γ commensurable with SL₂(ℤ), Nor(Γ) is conjugate into Γ₀(N)⁺ for some squarefree N |
| sanity | [`not_maximal_gamma0Plus_four`](NormalizerDelta/StatementsHelling.lean#L91) | Γ₀(4)⁺ is not maximal, so `gamma0Plus_maximal` needs N squarefree (Γ₀(4)⁺ lies in Nor(Γ₀(4)), a conjugate of SL₂(ℤ)) |

Sources: Helling [He], in the form of [Du, Theorem 2.11], where G_(1,N)+ is Γ₀(N)⁺ in PSL₂(ℝ). The proof follows
Conway's argument [Co], as presented in [Du, Proposition 2.10].

* G permutes a finite set of classes of lattices in ℚ², and at each prime p it fixes the centre of their image in
  the p-adic tree, which is a vertex or an edge.
* The Lean proof formalizes neither the trees nor the lattices. A vertex is an integral matrix X (the lattice
  Xℤ_(p)²). The distance of X and Y is d_p(adj(X)·Y), where d_p(Z) = v_p(det Z) − 2·v_p(the gcd of the entries of Z).
* The centres are glued over the primes with the Smith normal form.
* For Nor(Γ), the finite set is the set of vertices fixed by the elements of Γ whose representatives have square
  determinant.

## Building and checking

You need [elan](https://github.com/leanprover/elan). The Lean toolchain (v4.35.0-rc3) and Mathlib (v4.35.0-rc3) are
pinned in `lean-toolchain` and `lake-manifest.json`. The pin is the release candidate rather than v4.35.0 because
Palomar cannot yet render challenges on v4.35.0
([PalomarSubmission#161](https://github.com/PalomarRegistry/PalomarSubmission/issues/161)).

Every Lean file uses Lean's [module system](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/):
it starts with `module`, its imports are `public import`, and its declarations follow `@[expose] public section`,
so everything is public and every definition can be unfolded by the files that import it.
[`scripts/module_header.py`](scripts/module_header.py) adds exactly these lines and removes them again.

```sh
lake exe cache get                          # download the Mathlib build cache (about 8 GB in .lake/)
lake build NormalizerLean NormalizerDelta   # plain `lake build` builds only NormalizerLean (Part 1)
```

**Axioms.** Each of these prints `[propext, Classical.choice, Quot.sound]` for every theorem of the part. The
outputs are saved next to the scripts as `*_output.txt`.

```sh
lake env lean scripts/check_axioms.lean          # Part 1
lake env lean scripts/check_axioms_delta.lean    # Part 2
lake env lean scripts/check_axioms_extra.lean    # Part 3
lake env lean scripts/check_axioms_xn.lean       # Part 4
lake env lean scripts/check_axioms_cartan.lean   # Part 5
lake env lean scripts/check_axioms_general.lean  # Part 6
lake env lean scripts/check_axioms_star.lean     # Part 7
lake env lean scripts/check_axioms_mixed.lean    # Part 8
lake env lean scripts/check_axioms_helling.lean  # Part 9
```

A theorem that used `sorry` anywhere would show the axiom `sorryAx` here.

**Frozen statements.** [`frozen/`](frozen) holds each definitions and statements file as it was frozen, named by
the commit of the development repository, with `.txt` appended to the name (they are records, not Lean sources).
The scripts first remove the module-system header described above, then check that each statements file is the frozen one with each
`sorry` replaced by `by apply X' <;> assumption`, and that the frozen definitions of each part occur verbatim in
`NormalizerLean/Defs.lean` (for Part 1, the definitions region of the frozen `Statements.lean`).

```sh
for s in restructure delta_frozen extra_frozen xn_frozen cartan_frozen general_frozen star_frozen mixed_frozen \
         helling_frozen; do
  python3 scripts/check_$s.py
done
```

Each script prints `OK`.

* Its "sorry left: 1" counts the word "sorry" in the frozen file header "(Stage 0, all `sorry`)". The axiom check
  above is the test for actual `sorry`s.
* Some comments in the definitions and statements files were edited after freezing, in the same way in
  `frozen/`. The Lean code in `frozen/` is as frozen.
* After freezing, one definition was renamed in Part 6 (`fricke` to `frickeP`, a name clash with Part 1). The
  frozen Part 6 files are the ones after the rename.
* Parts 7, 8 and 9 were written in this repository, not in the development repository: their definitions and
  statements were frozen at commits a3e92bd, 54dcc6e and 7fc9442 of this repository
  ([`frozen/a3e92bd/`](frozen/a3e92bd), [`frozen/54dcc6e/`](frozen/54dcc6e), [`frozen/7fc9442/`](frozen/7fc9442)),
  and the proofs came after.

<a id="checking-with-comparator"></a>
**Checking with Comparator.** The statements form ten challenges, one for each part, with the B₀(N) theorems of
Part 3 in a challenge of their own; all but Part 3 B₀(N) and Part 4 have Palomar metadata
(`formalization.yaml`):

| part | challenge | solution | configuration and metadata | theorems |
|---|---|---|---|---|
| Part 1 | [`Challenge/Part1.lean`](Challenge/Part1.lean) | [`Solution/Part1.lean`](Solution/Part1.lean) | [`palomar/part1/`](palomar/part1) | 36 |
| Part 2 | [`Challenge/Part2.lean`](Challenge/Part2.lean) | [`Solution/Part2.lean`](Solution/Part2.lean) | [`palomar/part2/`](palomar/part2) | 34 |
| Part 3 | [`Challenge/Part3.lean`](Challenge/Part3.lean) | [`Solution/Part3.lean`](Solution/Part3.lean) | [`palomar/part3/`](palomar/part3) | 11 |
| Part 3, B₀(N) | [`Challenge/Part3B0.lean`](Challenge/Part3B0.lean) | [`Solution/Part3B0.lean`](Solution/Part3B0.lean) | [`palomar/part3_b0/`](palomar/part3_b0) (no Palomar metadata) | 3 |
| Part 4 | [`Challenge/Part4.lean`](Challenge/Part4.lean) | [`Solution/Part4.lean`](Solution/Part4.lean) | [`palomar/part4/`](palomar/part4) (no Palomar metadata) | 14 |
| Part 5 | [`Challenge/Part5.lean`](Challenge/Part5.lean) | [`Solution/Part5.lean`](Solution/Part5.lean) | [`palomar/part5/`](palomar/part5) | 17 |
| Part 6 | [`Challenge/Part6.lean`](Challenge/Part6.lean) | [`Solution/Part6.lean`](Solution/Part6.lean) | [`palomar/part6/`](palomar/part6) | 21 |
| Part 7 | [`Challenge/Part7.lean`](Challenge/Part7.lean) | [`Solution/Part7.lean`](Solution/Part7.lean) | [`palomar/part7/`](palomar/part7) | 20 |
| Part 8 | [`Challenge/Part8.lean`](Challenge/Part8.lean) | [`Solution/Part8.lean`](Solution/Part8.lean) | [`palomar/part8/`](palomar/part8) | 18 |
| Part 9 | [`Challenge/Part9.lean`](Challenge/Part9.lean) | [`Solution/Part9.lean`](Solution/Part9.lean) | [`palomar/part9/`](palomar/part9) | 9 |

Each challenge imports only Mathlib, so it is the complete specification of its part. It copies verbatim the parts
of [`NormalizerLean/Defs.lean`](NormalizerLean/Defs.lean) whose definitions its statements use, then the statements,
copied from the statements files with every proof replaced by `sorry`. The solution imports the statements files,
where the theorems are proved. With the entry's `comparator.json`,
[Comparator](https://github.com/leanprover/comparator) checks that each theorem has the same statement in the
challenge and in the solution, about the same definitions, uses no axioms other than `propext`, `Classical.choice`
and `Quot.sound`, and is accepted by the Lean kernel. In the pinned Lean version, Comparator is part of Lake. It
builds both modules itself, inside a [bubblewrap](https://github.com/containers/bubblewrap) sandbox, so `bwrap`
must be installed:

```sh
lake exe cache get
for e in part1 part2 part3 part3_b0 part4 part5 part6 part7 part8 part9; do
  lake comparator --config palomar/$e/comparator.json
done
```

With `--paranoid` it also replays the proofs with the independent checkers bundled with Lean (`nanoda`,
`lean4lean`, `con-leche`, `con-ron`). All ten challenges pass with `--paranoid`: every checker accepts, and
Comparator prints `Your solution is okay!`.

* Comparator compares the definitions as well as the statements: every definition a statement uses must be the same
  constant in the challenge and in the library, including the auxiliary lemmas inside it. The definitions contain no
  theorems apart from small lemmas used inside the definitions.
* Lean shares the auxiliary `_proof_n` lemmas of a file between its declarations, so a copy produces the library's
  constants only if it repeats the library's order. That is why all the definitions are in one file,
  `NormalizerLean/Defs.lean`, part by part, and each challenge copies whole parts of it, in order. The only
  auxiliary lemma used outside its own definition is `GammaDelta._proof_4` (Part 2), used in Parts 5 and 6, whose
  challenges therefore copy Part 2 as well. Two statements, in Parts 2 and 4, contain a proof of 7 ∣ 49; they are in
  different challenges, so that, as in the library, each gets its own lemma.
* [`scripts/make_challenge.py`](scripts/make_challenge.py) generates the challenges, the solutions and the
  configurations from `NormalizerLean/Defs.lean` and the statements files, and
  [`scripts/make_formalization.py`](scripts/make_formalization.py) generates each Palomar entry's `formalization.yaml` (the
  Palomar metadata) from the tables of this README. With `--check`, both check that their files are up to date.

**Numerical checks.** Before freezing, the statements were tested by brute force over ranges of N. The scripts
need Python 3; `check_xn_statements.py` also needs SymPy. Their outputs are saved next to them.

| script | checks |
|---|---|
| [`check_delta_statements.py`](scripts/check_delta_statements.py) | Part 2: the order for ±Γ₁(N) for N ≤ 400 (only N = 4 is an exception); the order for Γ_Δ(M²), M ≤ 18; the generalized Newman bound for every Δ ∋ −1, N ≤ 30 |
| [`check_delta_index.py`](scripts/check_delta_index.py) | Part 2: Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) if h_Δ = h(N), and the index, for every Δ ∋ −1, N ≤ 200; the S₇ example |
| [`check_delta_x1mn.py`](scripts/check_delta_x1mn.py) | Part 2: X_Δ(N) ≅ X₁(M, N/M), on all matrices with small entries |
| [`check_extra_statements.py`](scripts/check_extra_statements.py) | Part 3: h_Δ = h(N) iff none of (i)–(iii), for every Δ, N ≤ 300; uniqueness of (σ, H) for N ≤ 24 |
| [`check_xn_statements.py`](scripts/check_xn_statements.py) | Part 4: \|SL₂(ℤ/N)\| and the indices for N ≤ 16, \|PSL₂(ℤ/M)\|, the orders for X_Δ(M²), Δ = {±1 mod M}, at N = 49, …, 196 |
| [`check_cartan_statements.py`](scripts/check_cartan_statements.py) | Part 5: indices, invariant lines and [N(H̄) : H̄] for the four Cartan groups, p ≤ 13, and the witnesses at p = 5, 3 |
| [`check_star_statements.py`](scripts/check_star_statements.py) | Part 7: every statement, with the definitions implemented literally, for every Δ (with or without −1) and N ≤ 250, against the normalizer computed by brute force |
| [`check_general_statements.py`](scripts/check_general_statements.py) | Part 6: Nor(Γ_H)/Γ_H by brute force for every H up to conjugacy at N = 2, …, 11, against the general theorem, the prime-level results and Prop. 4.5 |
| [`check_mixed_statements.py`](scripts/check_mixed_statements.py) | Part 8: every statement, by brute force, for N₁ ∈ {1, 2, 3, 4, 5, 7, 8, 9} and every H₁ up to conjugacy, with H₂ = H_Δ for every Δ (N ≤ 30) or every H₂ up to conjugacy at N₂ ≤ 7 (N ≤ 36): 3716 cases, 66 of them with classes removed by Det(H₁); 143 cases for the corollaries; the Q₈ values |

[`aut_orders.py`](scripts/aut_orders.py) is the coset count used by the Part 2, 3 and 7 checks.

## Repository layout

```
NormalizerLean/          Part 1: Statements.lean and the proofs; Defs.lean, the definitions of all eight parts
NormalizerDelta/         Parts 2–9: Statements*.lean and the proofs; Defs*.lean only import NormalizerLean/Defs.lean
NormalizerLean.lean      root of Part 1
NormalizerDelta.lean     root of Parts 2–9
certs/                   certificates for the presentations (Magma and Python generators, JSON data)
frozen/<commit>/         the definitions and statements files as frozen (as .lean.txt)
Challenge/               the ten challenges: definitions and statements with `sorry`, for Comparator
Solution/                the ten solutions: they import the statements files
palomar/<challenge>/     comparator.json of each challenge; formalization.yaml (Palomar metadata) of each entry
scripts/                 axiom checks, frozen-statement checks, numerical checks, with their outputs
LICENSE                  Apache License 2.0
```

## Notes on the sources

* Comments in the Lean files cite three of the author's working notes, which are not in this repository: [Nw], a
  self-contained proof of Newman's theorem; [BA], presentations of B(N) at all levels; and [BAu], an audit of
  Bars's paper. Some comments also give paths under `~/automorphisms_X1/` for these notes.
* [DLM22] is cited with the numbering of arXiv:2005.09009v2, and [DLM26] with that of arXiv:2610.08998v1.
* This repository is a snapshot of a development repository. Commit hashes in `frozen/`, in the scripts and in
  comments refer to that repository, except a3e92bd (Part 7), 54dcc6e (Part 8) and 7fc9442 (Part 9), which are
  commits of this repository.

## References

* [AL] A. O. L. Atkin, J. Lehner, *Hecke operators on Γ₀(m)*, Math. Ann. 185 (1970), 134–160.
* [AS] M. Akbaş, D. Singerman, *The normalizer of Γ₀(N) in PSL(2, ℝ)*, Glasgow Math. J. 32 (1990), 317–327.
* [Bo] J. Box, *Computing models for quotients of modular curves*, Res. Number Theory 7 (2021), Paper No. 51,
  [arXiv:2101.03797](https://arxiv.org/abs/2101.03797).
* [Ba] F. Bars, *The group structure of the normalizer of Γ₀(N) after Atkin–Lehner*, Comm. Algebra 36 (2008),
  2160–2170.
* [Co] J. H. Conway, *Understanding groups like Γ₀(N)*, in *Groups, difference sets, and the Monster* (Columbus, OH,
  1993), de Gruyter, 1996, 327–343.
* [DLM22] V. Dose, G. Lido, P. Mercuri, *Automorphisms of Cartan modular curves of prime and composite level*,
  Algebra Number Theory 16 (2022), 1423–1461, [arXiv:2005.09009](https://arxiv.org/abs/2005.09009).
* [DLM26] V. Dose, G. M. Lido, P. Mercuri, *Automorphisms of general modular curves*,
  [arXiv:2610.08998](https://arxiv.org/abs/2610.08998).
* [Du] J. F. Duncan, *Arithmetic groups and the affine E8 Dynkin diagram*,
  [arXiv:0810.1465](https://arxiv.org/abs/0810.1465).
* [DN] M. Derickx, F. Najman, *Sporadic points on X₀(N)*, [arXiv:2511.09015](https://arxiv.org/abs/2511.09015).
* [He] H. Helling, *Bestimmung der Kommensurabilitätsklasse der Hilbertschen Modulgruppe*, Math. Z. 92 (1966),
  269–280.
* [KK] C. H. Kim, J. K. Koo, *The normalizer of Γ₁(N) in PSL₂(ℝ)*, Comm. Algebra 28 (2000), 5303–5310.
* [L] M.-L. Lang, *Normalizer of Γ₁(m)*, J. Number Theory 86 (2001), 50–60.
* [Ne] M. Newman, *Conjugacy, genus, and class numbers*, Math. Ann. 196 (1972), 198–217.
* [Ze] S. Zemel, *Normalizers of congruence groups in SL₂(ℝ) and automorphisms of lattices*, Int. J. Number Theory 13
  (2017), 1275–1300, [arXiv:1512.07547](https://arxiv.org/abs/1512.07547).

## License

Released under the [Apache License 2.0](LICENSE), the license of Mathlib.
