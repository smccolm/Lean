# Semisimple Rational Obstruction Conjecture - Sources

Status: source map and novelty boundary.

Research snapshot: 2026-09-08.

This document records the mathematical sources that define the known background and the boundary between established matrix-function theory and the specific fibre-injectivity problem studied here.

No absence-of-literature statement in this file is a novelty claim.

## 1. Object under study

For \(A\in GL_n(\mathbb C)\), define

```math
\mathrm{Log}(A)
=
\{L\in M_n(\mathbb C):\exp(L)=A\},
```

and

```math
\Phi_A(L)=\exp(AL).
```

The project asks for an exact criterion for injectivity of \(\Phi_A\) on the **entire** logarithm fibre.

The current candidate theorem is

```math
\Phi_A\text{ injective}
\iff
\forall\lambda\in\sigma(A)\cap\mathbb Q,\quad
\dim\ker(A-\lambda I)=1
\ \land\
\ker(A-\lambda I)\subseteq\operatorname{im}(A-\lambda I).
```

Equivalently, every rational eigenvalue must have exactly one Jordan block, and that block must have size at least \(2\).

## 2. Classical matrix-logarithm theory

### Gantmacher

F. R. Gantmacher, *The Theory of Matrices*, Volumes I and II.

Use for:

- Jordan canonical form;
- centralizers of Jordan forms;
- logarithms of nonsingular matrices;
- branch choices on Jordan blocks;
- nonprimary freedom for derogatory matrices.

Project rule: if an assertion is merely an application of the all-logarithms classification, it is not to be presented as a new theorem.

### Higham

Nicholas J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008.

Matrix logarithm chapter:

https://doi.org/10.1137/1.9780898717778.ch11

Use for:

- modern primary/nonprimary matrix-function language;
- principal logarithm;
- Jordan and interpolation definitions;
- logarithm existence and uniqueness results;
- attribution of the general all-logarithms description to classical sources.

Supplementary exposition:

Nicholas J. Higham, "What Is the Matrix Logarithm?", 2020.

https://nhigham.com/2020/11/17/what-is-the-matrix-logarithm/

Use for compact examples of multiple and nonprimary logarithms.

## 3. Matrix-matrix exponentiation

### Barradas and Cohen, 1994

Ignacio Barradas and Joel E. Cohen,
"Iterated Exponentiation, Matrix-Matrix Exponentiation, and Entropy",
*Journal of Mathematical Analysis and Applications* 183 (1994), 76-88.

Author-hosted PDF:

https://lab.rockefeller.edu/cohenje/assets/file/215BarrabasCohenJMathAnalApp1994.pdf

Use for:

- early explicit matrix-matrix exponentiation;
- normal nonsingular matrices;
- the distinction between scalar and matrix exponentiation.

Boundary: this is not an all-logarithms fibre-injectivity study.

### Cardoso and Sadeghi, 2018

Joao R. Cardoso and Amir Sadeghi,
"Conditioning of the matrix-matrix exponentiation",
*Numerical Algorithms* 79 (2018), 565-581.

DOI:

https://doi.org/10.1007/s11075-017-0446-2

Preprint:

https://arxiv.org/abs/1703.08804

Use for:

- modern matrix-matrix exponentiation
  ```math
  A^B=\exp(\log(A)B),
  ```
  with the principal logarithm;
- Frechet derivative;
- conditioning.

Boundary: their selected principal logarithm suppresses the full fibre \(\mathrm{Log}(A)\) that is central here.

## 4. Branch bookkeeping

### Aprahamian and Higham, 2014

Mary Aprahamian and Nicholas J. Higham,
"The Matrix Unwinding Function, with an Application to Computing the Matrix Exponential",
*SIAM Journal on Matrix Analysis and Applications* 35 (2014), 88-109.

DOI:

https://doi.org/10.1137/130920137

Use for:

- matrix unwinding;
- branch corrections;
- identities involving logarithms and powers;
- exact representation of branch information discarded by principal values.

Project rule: "principalization loses branch information" is already established territory.

## 5. Related multivalued inverse-function precedent

### Corless, Ding, Higham, Jeffrey

Robert M. Corless, Hui Ding, Nicholas J. Higham, and David J. Jeffrey,
"The Solution of \(S\exp(S)=A\) is Not Always the Lambert \(W\) Function of \(A\)",
ISSAC 2007.

DOI:

https://doi.org/10.1145/1277548.1277565

Use for:

- precedent that evaluating a named matrix function need not classify all matrix solutions of the underlying matrix equation;
- methodological warning against conflating a selected matrix function with a full solution fibre.

This precedent is conceptually relevant to studying the entire logarithm fibre rather than only the principal branch.

## 6. Lean / Mathlib sources to inspect

The project should inspect the installed Mathlib version before creating local substitutes.

Likely useful areas include:

```text
Mathlib/Analysis/Normed/Algebra/MatrixExponential
Mathlib/LinearAlgebra/Matrix
Mathlib/LinearAlgebra/Eigenspace
Mathlib/LinearAlgebra/InvariantBasisNumber
Mathlib/LinearAlgebra/JordanChevalley
Mathlib/LinearAlgebra/Matrix/Polynomial
Mathlib/FieldTheory
Mathlib/Data/Complex/Exponential
Mathlib/NumberTheory/Real/Irrational
```

Exact module names may differ in the installed version. Search Mathlib before adding local infrastructure.

Useful existing families expected to matter:

- matrix exponential;
- exponential under similarity/conjugation;
- exponential of commuting sums;
- complex exponential periodicity;
- nilpotent matrix powers;
- generalized eigenspaces;
- finite-dimensional linear equivalences;
- minimal polynomial machinery;
- diagonalizable / semisimple machinery;
- integer and rational coercions into \(\mathbb C\).

## 7. Exact results that are already not research claims

Do not present these as novel:

1. A nonsingular matrix can have infinitely many logarithms.
2. Nonprimary logarithms occur in derogatory settings.
3. The principal logarithm chooses one branch.
4. Principal branch selection discards branch information.
5. If \(K\) is diagonalizable with integer eigenvalues, then
   ```math
   \exp(2\pi iK)=I.
   ```
6. Conversely, over \(\mathbb C\),
   ```math
   \exp(2\pi iK)=I
   ```
   forces \(K\) to be diagonalizable with integer eigenvalues.
7. Irrational rotations have dense orbits on the circle.
8. A single nontrivial Jordan block has polynomial centralizer.
9. If a rational eigenvalue appears in multiple Jordan blocks, the centralizer contains inter-block maps.

These are infrastructure.

## 8. Current research boundary

The specific map

```math
\Phi_A:\mathrm{Log}(A)\to GL_n(\mathbb C),
\qquad
L\mapsto\exp(AL)
```

and the equivalence relation

```math
L_1\sim_A L_2
\iff
\exp(AL_1)=\exp(AL_2)
```

are the objects to search for directly.

Targeted literature review should search for exact or equivalent formulations under phrases including:

```text
all matrix logarithms self exponentiation
matrix logarithm fibre injectivity
matrix logarithm fiber injectivity
exp(AL) exp(L)=A
distinct logarithms same matrix power
nonprimary logarithm exponentiation
matrix self exponentiation all branches
matrix exponential fibre quotient
matrix exponential fiber quotient
```

Also search cited references backward from Gantmacher, Higham, Aprahamian-Higham, Barradas-Cohen, Cardoso-Sadeghi, and Corless et al.

## 9. Novelty rule

A theorem may be called new only after all of the following:

- Lean proof complete;
- paper proof complete;
- theorem reduced to a basis-independent statement;
- targeted searches for exact and equivalent formulations;
- backward citation search through classical logarithm literature;
- forward citation search from matrix-matrix exponentiation and unwinding papers;
- no source found that states the theorem or an obviously equivalent result;
- no source found from which the theorem is an immediate named corollary that would make a novelty claim misleading.

Until then use:

```text
candidate theorem
candidate result
formal target
apparently unstated consequence
```

Never use:

```text
new theorem
novel theorem
first proof
previously unknown
```
