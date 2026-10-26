# A Rank-Two Witness Reduction of the Ramanujan–Petersson Bound (after Deligne)

**Author.** Lior Isthmus  
**Date.** 2026-02-20

## Abstract

We give a short derivation of the Ramanujan-Petersson bound for normalized holomorphic newforms by isolating a rank-two witness whose Frobenius trace equals the Hecke eigenvalue at unramified primes, and then applying a one-line squeeze using purity. An appendix records the standard geometric input: realization of the witness in étale cohomology of modular curves with symmetric-power local systems (or via Kuga–Sato varieties), the Hecke–Frobenius compatibility giving the local Euler factor, and the purity statement used in the squeeze. This note is expository: we do not reprove Deligne’s construction of $\rho_{f,\ell}$ or Weil II; we only isolate the minimal inputs needed for the bound.

---

<div id="sec:introduction"></div>

## 1. Introduction

A common arithmetic pattern is to realize a scalar quantity as the trace of an operator acting on a small-dimensional space and then bound the trace by controlling the spectral radius. In the modular setting, the Hecke eigenvalue $a_p$ at an unramified prime $p$ is the trace of Frobenius acting on a rank-two $\ell$-adic Galois representation. Deligne's purity theorem forces both Frobenius eigenvalues to have absolute value $p^{(k-1)/2}$, and the Ramanujan-Petersson bound follows immediately from the triangle inequality. The proof thus decomposes into (i) existence and Hecke-Frobenius compatibility of the representation, and (ii) purity. We refer to this three-step reduction (rank-two witness, purity, and the elementary trace bound) as a witness–squeeze argument.

---

<div id="sec:setup-statement"></div>

## 2. Setup and Statement

Let $k \ge 2$, $N \ge 1$, and let $\chi:(\mathbb Z/N\mathbb Z)^\times \to \mathbb C^\times$ be a Dirichlet character (nebentypus). Let $f(z)=\sum_{n\ge 1} a_n q^n$ with $q=e^{2\pi i z}$ be a normalized cuspidal newform of weight $k$, level $\Gamma_0(N)$, and nebentypus $\chi$, so $a_1=1$ and for each prime $p\nmid N$,

$$
T_p f = a_p f.
$$

Let $E_f:=\mathbb{Q}(\{a_n\}_{n\ge 1},\mathrm{Im}(\chi))\subset\mathbb{C}$ be the Hecke field of $f$. It is a number field and $a_n\in E_f$ for all $n$. We fix the embedding $E_f\hookrightarrow\mathbb{C}$ for which the above $q$-expansion is written. For each prime $\ell$ we also fix an embedding $\iota_\ell:E_f\hookrightarrow\overline{\mathbb{Q}}_\ell$; when forming $\ell$-adic statements we silently view $a_n$ and $\chi(d)$ via $\iota_\ell$.
We include $\mathrm{Im}(\chi)$ for notational convenience, so that $\chi(p)\in E_f$.
Fix an algebraic closure $\overline{\mathbb{Q}}\subset\mathbb{C}$ of $\mathbb{Q}$ containing $E_f$, and use it throughout.

<div id="thm:ramanujan-petersson-unramified"></div>

**Theorem 2.1 (Ramanujan-Petersson / Deligne, unramified primes).**
For every prime $p\nmid N$,

$$
|a_p| \le 2p^{(k-1)/2}.
$$ {#eq:ramanujan-bound}

<div id="rem:ramified-primes"></div>

**Remark 2.2.**
At primes $p\mid N$, the local representation is ramified and the local $L$-factor has degree $<2$ (often $1$ or $0$), so the unramified Satake-parameter picture used here does not apply; see [DS05].

---

<div id="sec:rank-two-witness"></div>

## 3. The Rank-Two Witness: An $\ell$-Adic Representation

Fix a prime $\ell$ and view $E_f$ inside $\overline{\mathbb{Q}}_\ell$ via $\iota_\ell$ (§2). Let $G_{\mathbb Q}=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. For $p\nmid N\ell$ we write $\mathrm{Frob}_p$ for a *geometric* Frobenius element (inverse to arithmetic Frobenius on the residue field), defined up to conjugacy.

<div id="thm:deligne-existence-charpoly"></div>

**Theorem 3.1 (Deligne [Del69]; existence and local characteristic polynomial).**
There exists a continuous semisimple representation

$$
\rho_{f,\ell}:G_{\mathbb Q}\longrightarrow \mathrm{GL}_2(\overline{\mathbb Q}_\ell),
$$

unramified outside $N\ell$, such that for each prime $p\nmid N\ell$,

$$
\det\!\bigl(1 - X\cdot \rho_{f,\ell}(\mathrm{Frob}_p)\bigr)
= 1 - a_p X + \chi(p)p^{k-1}X^2.
$$ {#eq:local-charpoly}

(Here $a_p$ and $\chi(p)$ are viewed in $\overline{\mathbb{Q}}_\ell$ via $\iota_\ell$ as fixed in §2.)

In particular,

$$
\mathrm{Tr}\bigl(\rho_{f,\ell}(\mathrm{Frob}_p)\bigr)=a_p,\qquad
\det\bigl(\rho_{f,\ell}(\mathrm{Frob}_p)\bigr)=\chi(p)p^{k-1}.
$$

We refer to $\rho_{f,\ell}(\mathrm{Frob}_p)$ as a rank-two witness for $a_p$.

---

<div id="sec:purity"></div>

## 4. Purity: Control of the Spectral Radius

<div id="thm:deligne-purity-unramified"></div>

For each prime $p\nmid N$, let $\alpha_p,\beta_p\in\overline{\mathbb{Q}}\subset\mathbb{C}$ be the roots of the Hecke polynomial

$$
T^2-a_pT+\chi(p)p^{k-1}=(T-\alpha_p)(T-\beta_p).
$$

(Thus $a_p=\alpha_p+\beta_p$ and $\alpha_p\beta_p=\chi(p)p^{k-1}$ in $\overline{\mathbb{Q}}$.)
Equivalently, by Theorem 3.1, for any prime $\ell$ with $p\nmid N\ell$ (equivalently, $\ell\neq p$ since $p\nmid N$), the characteristic polynomial of $\rho_{f,\ell}(\mathrm{Frob}_p)$ is $T^2-a_pT+\chi(p)p^{k-1}$; hence its eigenvalues are roots of this polynomial (in $\overline{\mathbb{Q}}_\ell$), so Theorem 4.1 is precisely the purity statement for the rank-two witness.

**Theorem 4.1 (Deligne [Del80]; purity at unramified primes).**
For every prime $p\nmid N$ and every embedding $\sigma:\overline{\mathbb{Q}}\hookrightarrow\mathbb{C}$,

$$
|\sigma(\alpha_p)| = |\sigma(\beta_p)| = p^{(k-1)/2}.
$$ {#eq:purity-weights}

---

<div id="sec:proof-witness-squeeze"></div>

## 5. Proof and a Rank-Two Trace Bound

<div id="sec:proof-theorem-2-1"></div>

*Proof.* Fix a prime $p\nmid N$ and let $\alpha_p,\beta_p$ be as in Theorem 4.1, so $a_p=\alpha_p+\beta_p$. Applying \eqref{eq:purity-weights} with $\sigma$ the fixed inclusion $\overline{\mathbb{Q}}\hookrightarrow\mathbb{C}$, we have $|\alpha_p|=|\beta_p|=p^{(k-1)/2}$. Hence

$$
|a_p| = |\alpha_p+\beta_p|
\le |\alpha_p| + |\beta_p|
= 2p^{(k-1)/2}.
$$

The final inequality is the rank-two trace bound recorded as Lemma 5.1.
This proves Theorem 2.1. ∎

<div id="lem:witness-squeeze-rank-two"></div>

**Lemma 5.1 (Rank-two trace bound).**
Let $a\in \mathbb C$. Suppose there exist $\alpha,\beta\in \mathbb C$ such that $a=\alpha+\beta$ and

$$
|\alpha|\le R,\qquad |\beta|\le R
$$

for some $R\ge 0$. Then $|a|\le 2R$.

We record this elementary inequality only to make the dependence on rank explicit.

*Proof.* $|a|=|\alpha+\beta|\le|\alpha|+|\beta|\le 2R$. ∎

<div id="rem:witness-squeeze-application"></div>

**Remark 5.2.**
In Theorem 2.1, for any $\ell$ with $p\nmid N\ell$, the witness is $\rho_{f,\ell}(\mathrm{Frob}_p)$, and purity gives $R=p^{(k-1)/2}$. The constant $2$ is forced by the rank-two witness.

<div id="cor:prime-powers"></div>

**Corollary 5.3 (Prime powers and coprime indices).**
Assume $p\nmid N$ and let $m\ge 0$. Then

$$
|a_{p^m}|\le (m+1)\,p^{m(k-1)/2}.
$$

In particular, if $(n,N)=1$ then

$$
|a_n|\le d(n)\,n^{(k-1)/2},
$$

where $d(n)$ denotes the number of positive divisors of $n$.

*Proof.* For $p\nmid N$ we have

$$
(1-a_pX+\chi(p)p^{k-1}X^2)^{-1}
= \sum_{m\ge 0} a_{p^m}X^m
= \bigl((1-\alpha_pX)(1-\beta_pX)\bigr)^{-1}.
$$

Comparing coefficients gives $a_{p^m}=\sum_{j=0}^{m}\alpha_p^{\,j}\beta_p^{\,m-j}$, hence
$|a_{p^m}|\le \sum_{j=0}^{m}|\alpha_p|^{j}|\beta_p|^{m-j}=(m+1)p^{m(k-1)/2}$ by Theorem 4.1.
For $(n,N)=1$, writing $n=\prod_i p_i^{m_i}$ gives

$$
a_n=\prod_i a_{p_i^{m_i}}.
$$

Hence

$$
|a_n|\le \prod_i (m_i+1)p_i^{m_i(k-1)/2}=d(n)\,n^{(k-1)/2}.
$$

∎

---

<div id="sec:appendix-a-construction"></div>

## Appendix A. From Local Systems (or Kuga–Sato) to $\rho_{f,\ell}$ and the Local Factor

This appendix records the standard geometric input underlying Theorems 3.1 and 4.1. We spell out the formal implications (e.g. how trace and determinant recover the Euler factor); deeper inputs from Deligne's construction of $\rho_{f,\ell}$ and from Weil II are stated precisely and referenced.

In particular, we explain how the unramified local factor

$$
1 - a_p X + \chi(p)p^{k-1}X^2 \qquad (p\nmid N)
$$

arises from geometric Frobenius acting on an appropriate two-dimensional cohomological eigenspace.

### A.1 Modular Curves and the Symmetric-Power Local System

Let $Y=Y_1(N)$ be the open modular curve over $\mathbb{Q}$ parameterizing elliptic curves with $\Gamma_1(N)$-level structure, and let $X=X_1(N)$ be its smooth compactification; write $j:Y\hookrightarrow X$. (For small $N$, one should interpret $Y_1(N)$ as a modular Deligne-Mumford stack, or else replace the level by a sufficiently fine auxiliary level; this point is inessential for the present note.) Over $Y$ there is a universal elliptic curve $\pi:\mathcal{E}\to Y$.

Fix a prime $\ell$. Consider the lisse $\overline{\mathbb Q}_\ell$-sheaf

$$
\mathcal H_\ell := R^1\pi_*\overline{\mathbb Q}_\ell
$$

on $Y_{\overline{\mathbb Q}}$, whose fiber at a geometric point corresponds to $H^1_{\mathrm{\acute et}}(E_{\overline{\mathbb Q}},\overline{\mathbb Q}_\ell)$. For weight $k\ge 2$, define the symmetric-power local system

$$
\mathcal V_{k-2,\ell} := \mathrm{Sym}^{k-2}(\mathcal H_\ell),
$$

which admits a middle extension to $X$ (denoted $j_{!*}\mathcal V_{k-2,\ell}$; see [BBD82] for the general formalism; for curves the parabolic model below suffices).

Equivalently, one may work with interior (parabolic) cohomology

$$
H^1_!(Y_{\overline{\mathbb{Q}}},\mathcal{V}_{k-2,\ell})
:=\mathrm{Im}\Bigl(H^1_c(Y_{\overline{\mathbb{Q}}},\mathcal{V}_{k-2,\ell})\to H^1(Y_{\overline{\mathbb{Q}}},\mathcal{V}_{k-2,\ell})\Bigr),
$$

which canonically identifies with $H^1_{\acute et}(X_{\overline{\mathbb{Q}}},j_{!*}\mathcal{V}_{k-2,\ell})$ for curves (see [BBD82]).

<div id="rem:interior-cohomology-model"></div>

**Remark A.1 (Interior cohomology model).**
For curves, the middle-extension model and parabolic cohomology model agree canonically; we mention both to accommodate different conventions.

By functoriality, $H^1_{\acute et}(X_{\overline{\mathbb Q}},j_{!*}\mathcal V_{k-2,\ell})$ carries a continuous action of $G_{\mathbb Q}$. Hecke correspondences and diamond operators define commuting endomorphisms; we record the resulting $G_{\mathbb Q}$-equivariant Hecke action in §A.2, and we state Deligne's cohomological realization of $\rho_{f,\ell}$ in §A.3.

### A.2 Hecke Correspondences and Hecke Action on Cohomology

**Proposition A.2 (Hecke and diamond actions).**
For each prime $p\nmid N$, the Hecke correspondence defining $T_p$ induces a $G_{\mathbb Q}$-equivariant endomorphism of the cohomology group.

$$
H^1_{\acute et}(X_{\overline{\mathbb Q}},j_{!*}\mathcal V_{k-2,\ell})
$$

Diamond operators $\langle d\rangle$ act similarly. Moreover, the $\Gamma_0(N)$-nebentypus $\chi$ condition corresponds to passing to the $\chi$-isotypic subspace for the diamond action: $\langle d\rangle v=\chi(d)v$ for all $d\in(\mathbb{Z}/N\mathbb{Z})^\times$.

*Proof.* The correspondence defining $T_p$ is defined over $\mathbb Q$. The induced endomorphism on étale cohomology is given by the usual pull–push along the correspondence, and functoriality makes both pullback and proper pushforward $G_{\mathbb Q}$-equivariant; hence so is their composition. See, for instance, [Shim71, DS05] for the correspondence description of Hecke operators. ∎

### A.3 The $f$-Isotypic Component and the Galois Representation

Let $\mathbb T$ be the Hecke algebra generated by $T_p$ for $p\nmid N$ together with diamond operators. A normalized eigen-newform $f$ determines a character of $\mathbb T$ by $T_p\mapsto a_p$ and $\langle d\rangle\mapsto \chi(d)$. Let $\mathfrak m_f\subset\mathbb T$ be the maximal ideal determined by $(T_p-a_p)$ and $(\langle d\rangle-\chi(d))$. Define $V_{f,\ell}$ as the localization at $\mathfrak m_f$ (equivalently, the $f$-isotypic component after extension of scalars):

$$
V_{f,\ell}:=H^1_{\acute et}(X_{\overline{\mathbb Q}},j_{!*}\mathcal V_{k-2,\ell})_{\mathfrak m_f}.
$$

**Theorem A.3 (Deligne; cohomological realization of $\rho_{f,\ell}$).**
The space $V_{f,\ell}$ is two-dimensional, stable under $G_{\mathbb Q}$, and the induced $G_{\mathbb Q}$-action is (after semisimplification) the representation $\rho_{f,\ell}$ of Theorem 3.1. In particular, $\rho_{f,\ell}$ is unramified outside $N\ell$, and for every prime $p\nmid N\ell$,

$$
\det\!\bigl(1-X\,\rho_{f,\ell}(\mathrm{Frob}_p)\bigr)
=1-a_pX+\chi(p)p^{k-1}X^2.
$$

*Reference.* See Deligne [Del69]. For expository accounts (including constructions via Kuga–Sato varieties) see Scholl [Sch90] and Diamond–Shurman [DS05].

### A.4 Recovering the Local Euler Factor

**Corollary A.4 (Local Euler factor).**
For $p\nmid N\ell$,

$$
\det\bigl(1-X\rho_{f,\ell}(\mathrm{Frob}_p)\bigr)=1-a_pX+\chi(p)p^{k-1}X^2,
$$

which is the unramified Euler polynomial; equivalently the local $L$-factor is its reciprocal after substituting $X=p^{-s}$.

*Proof.* Immediate from Theorem A.3. ∎

**Remark A.5 (Eichler–Shimura congruence).**
The same Hecke–Frobenius compatibility is often expressed as an operator relation on cohomology

$$
\mathrm{Frob}_p^2 - T_p\,\mathrm{Frob}_p + p^{k-1}\langle p\rangle = 0,
$$

(with $\mathrm{Frob}_p$ geometric), see e.g. [Shim71, DS05]. On the $(f,\chi)$-isotypic component this becomes
$\mathrm{Frob}_p^2-a_p\mathrm{Frob}_p+\chi(p)p^{k-1}=0$, showing in particular that the Frobenius eigenvalues are roots of the Hecke polynomial. In weight $k=2$ this reads
$T_p=\mathrm{Frob}_p+p\langle p\rangle\,\mathrm{Frob}_p^{-1}$.

This congruence relation provides an alternative route to the polynomial in Theorem A.3 (hence Theorem 3.1).

### A.5 Purity and the Ramanujan-Petersson Bound

**Theorem A.6 (Deligne [Del80]; purity of the cohomological realization).**
The $G_{\mathbb Q}$-representation $V_{f,\ell}$ (hence $\rho_{f,\ell}$) is pure of weight $k-1$. In particular, for each prime $p\nmid N\ell$, if $\alpha_p,\beta_p\in\overline{\mathbb Q}\subset\mathbb C$ are the roots of $T^2-a_pT+\chi(p)p^{k-1}$, then for every embedding $\sigma:\overline{\mathbb Q}\hookrightarrow\mathbb C$,

$$
|\sigma(\alpha_p)|=|\sigma(\beta_p)|=p^{(k-1)/2}
$$

*Proof.* At good primes, $\mathcal H_\ell=R^1\pi_*\overline{\mathbb Q}_\ell$ is pure of weight $1$, hence
$\mathcal V_{k-2,\ell}=\mathrm{Sym}^{k-2}(\mathcal H_\ell)$ is pure of weight $k-2$.
Deligne's theory of weights [Del80] implies that for a lisse sheaf $\mathcal F$ pure of weight $w$ on a smooth curve $Y$, the group
$H^1_c(Y_{\overline{\mathbb Q}},\mathcal F)$ has weights $\le w+1$ while
$H^1(Y_{\overline{\mathbb Q}},\mathcal F)$ has weights $\ge w+1$; therefore their image
$H^1_!(Y_{\overline{\mathbb Q}},\mathcal F)=\mathrm{Im}(H^1_c\to H^1)$ is pure of weight $w+1$.
Applying this with $\mathcal F=\mathcal V_{k-2,\ell}$ gives purity of weight $(k-2)+1=k-1$ on $H^1_!(Y_{\overline{\mathbb Q}},\mathcal V_{k-2,\ell})$ and hence on its $f$-isotypic summand $V_{f,\ell}$, yielding the stated absolute value. ∎

---

## References

[Del69] P. Deligne, "Formes modulaires et représentations $\ell$-adiques", *Séminaire Bourbaki* (1968/69), Exp. 355; in *Lecture Notes in Mathematics* 179, Springer (1971), 139-172.

[Del80] P. Deligne, "La conjecture de Weil. II", *Publications Mathématiques de l'IHÉS* 52 (1980), 137-252. DOI: 10.1007/BF02684780.

[BBD82] A. A. Beilinson, J. Bernstein, and P. Deligne, *Faisceaux pervers*, *Astérisque* 100, Société Mathématique de France (1982).

[DS05] F. Diamond and J. Shurman, *A First Course in Modular Forms*, *Graduate Texts in Mathematics* 228, Springer (2005).

[Sch90] A. J. Scholl, "Motives for modular forms", *Inventiones Mathematicae* 100 (1990), 419-430. DOI: 10.1007/BF01231194.

[Shim71] G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, *Publications of the Mathematical Society of Japan* 11, Iwanami Shoten and Princeton University Press (1971).
