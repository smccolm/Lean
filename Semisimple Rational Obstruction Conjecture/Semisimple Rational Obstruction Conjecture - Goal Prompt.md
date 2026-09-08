# Semisimple Rational Obstruction Conjecture - Goal Prompt

You are working inside:

```text
E:\Lean\Semisimple Rational Obstruction Conjecture
```

Your job is to adversarially formalize the matrix-logarithm fibre injectivity problem described below.

Do not assume the target theorem is true. Try to break it as you formalize it.

## Primary object

For a nonsingular complex matrix \(A\), define

```math
\mathrm{Log}(A)=\{L:\exp(L)=A\}
```

and

```math
\Phi_A(L)=\exp(AL).
```

The current candidate theorem is:

```math
\Phi_A\text{ is injective}
\iff
\forall\lambda\in\sigma(A)\cap\mathbb Q,\quad
\dim\ker(A-\lambda I)=1
\ \land\
\ker(A-\lambda I)\subseteq\operatorname{im}(A-\lambda I).
```

Equivalent Jordan statement:

> Every rational eigenvalue occurs in exactly one Jordan block, and that block has size at least \(2\).

This is a candidate theorem only.

## First mandatory task: certify the dead conjecture

Before touching the repaired theorem, formalize the exact \(4\times4\) counterexample to the earlier criterion.

Use

```math
N=
\begin{bmatrix}
0&1\\
0&0
\end{bmatrix},
\qquad
J=I_2+N,
\qquad
A=J\oplus J.
```

Set

```math
X=
\begin{bmatrix}
N&0\\
0&N+2\pi iI_2
\end{bmatrix},
```

```math
U=
\begin{bmatrix}
I_2&N\\
0&I_2
\end{bmatrix},
\qquad
Y=UXU^{-1}.
```

Prove:

```math
X\ne Y,
```

```math
\exp(X)=A,
```

```math
\exp(Y)=A,
```

```math
\exp(AX)=\exp(AY),
```

```math
\ker(A-I)=\operatorname{im}(A-I).
```

This theorem must remain in the final project permanently.

## Main reduction

Fix one primary logarithm \(L_0\) when needed.

For any \(L\in\mathrm{Log}(A)\), study

```math
K=\frac{L-L_0}{2\pi i}.
```

The intended branch-operator facts are:

```math
KA=AK,
```

```math
\exp(2\pi iK)=I,
```

and therefore

```math
K\text{ is diagonalizable with integer spectrum}.
```

Use this to reduce the problem to

```math
\Psi_A(K)=\exp(2\pi iAK).
```

On a generalized eigenspace,

```math
A=\lambda I+N,
```

so

```math
\Psi_A(K)
=
\exp(2\pi i\lambda K)
\exp(2\pi iNK).
```

The working prediction is:

1. \(\lambda\notin\mathbb Q\): injective for arbitrary Jordan structure.
2. Rational \(\lambda\), one \(1\times1\) block: noninjective.
3. Rational \(\lambda\), one block of size at least \(2\): injective.
4. Rational \(\lambda\), multiple blocks: noninjective.

Prove or falsify these one at a time.

## Required research behavior

- Search Mathlib before inventing infrastructure.
- Prefer exact finite-dimensional algebra over analytic abstractions.
- Keep every theorem statement basis-independent when practical.
- Explicit Jordan matrices are allowed for counterexamples and local lemmas.
- Do not replace an exact matrix theorem with floating-point evidence.
- Do not introduce `sorry`.
- Do not weaken the theorem merely to make Lean accept it.
- If the theorem is false, stop the proof attempt, formalize the counterexample, and repair the statement only after identifying the failed mechanism.
- Preserve failed conjectures and their counterexamples as permanent regression tests.
- Treat Gantmacher/Higham matrix-logarithm theory as prior art.
- Never use the word "new" in theorem comments or README claims unless a separate completed literature audit supports it.

## Anti-token-furnace constraints

Do not undertake:

- a classification of all matrix logarithms from first principles;
- a classification of all fibres of \(\Phi_A\);
- arbitrary singular-matrix self-powers;
- Riemann surfaces;
- numerical condition numbers;
- arbitrary \(A^B\);
- general operator-theoretic extensions.

Formalize only what is consumed by the injectivity theorem or its counterexample.

## Suggested module order

```text
SemisimpleRationalObstruction/
  Basic.lean
  MatrixLogFiber.lean
  Counterexample4x4.lean
  BranchOperator.lean
  LocalNonrational.lean
  LocalRationalSingleJordan.lean
  LocalRationalMultipleJordan.lean
  GlobalAssembly.lean
  Main.lean
  Audit.lean
```

The exact module split may change if Mathlib dependencies make another split materially cleaner.

## Success condition

Success is one of:

### A. theorem survives

A no-`sorry`, full-build Lean proof of the repaired injectivity iff criterion, together with the formalized \(4\times4\) counterexample to the earlier conjecture.

### B. theorem dies

A no-`sorry` exact Lean counterexample to the repaired criterion, plus a precise account of the failed proof gate.

A counterexample is not failure.

The worst outcome is spending a long campaign proving a statement only because the formalization silently excluded the logarithms that make it false.
