# Semisimple Rational Obstruction Conjecture

Status: active research/formalization project.

This directory studies the information retained by matrix self-exponentiation when **all** matrix logarithms are admitted.

For a nonsingular complex matrix \(A\), define

```math
\mathrm{Log}(A)
=
\{L\in M_n(\mathbb C):\exp(L)=A\},
```

and

```math
\Phi_A:\mathrm{Log}(A)\to GL_n(\mathbb C),
\qquad
\Phi_A(L)=\exp(AL).
```

The central question is:

> When is \(\Phi_A\) injective?

Equivalently, when can two distinct matrix logarithms of the same matrix become indistinguishable after self-exponentiation?

## Current status

The first conjecture proposed for this problem was false.

It claimed that injectivity should fail precisely when a rational eigendirection is semisimple. The following exact \(4\times4\) construction falsifies that criterion even though every rational eigendirection belongs to a nontrivial Jordan chain.

Let

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

Then

```math
\ker(A-I)=\operatorname{im}(A-I).
```

Define

```math
X=
\begin{bmatrix}
N&0\\
0&N+2\pi iI_2
\end{bmatrix},
\qquad
U=
\begin{bmatrix}
I_2&N\\
0&I_2
\end{bmatrix},
\qquad
Y=UXU^{-1}.
```

One obtains

```math
X\ne Y,
\qquad
\exp(X)=\exp(Y)=A,
\qquad
\exp(AX)=\exp(AY).
```

Thus the original criterion is false.

The failure comes from repeated Jordan chains at the same rational eigenvalue. The centralizer of \(A\) contains transformations that move logarithm information between equal Jordan blocks while leaving the resulting self-power unchanged.

## Repaired candidate theorem

The present target is:

```math
\Phi_A\text{ is injective}
\iff
\forall\lambda\in\sigma(A)\cap\mathbb Q,\quad
\dim\ker(A-\lambda I)=1
\ \land\
\ker(A-\lambda I)\subseteq\operatorname{im}(A-\lambda I).
```

Equivalently:

> For every rational eigenvalue \(\lambda\), the generalized \(\lambda\)-eigenspace consists of exactly one Jordan block, and that block has size at least \(2\).

This is a **candidate theorem**, not an established theorem and not a novelty claim.

The project must try to falsify it before treating it as a theorem.

## Branch-operator reduction

Fix one primary logarithm \(L_0\) of \(A\).

For any \(L\in\mathrm{Log}(A)\), define

```math
K=\frac{L-L_0}{2\pi i}.
```

The intended reduction is that \(K\):

- commutes with \(A\);
- is diagonalizable;
- has integer spectrum;
- satisfies
  ```math
  L=L_0+2\pi iK.
  ```

Then

```math
\Phi_A(L)
=
\exp(AL_0)\exp(2\pi iAK).
```

Since \(\exp(AL_0)\) is fixed and invertible, injectivity of \(\Phi_A\) reduces to injectivity of

```math
\Psi_A(K)=\exp(2\pi iAK)
```

on the admissible branch operators \(K\).

On the generalized eigenspace for \(\lambda\),

```math
A=\lambda I+N
```

with nilpotent \(N\), and

```math
\Psi_A(K)
=
\exp(2\pi i\lambda K)\,
\exp(2\pi iNK).
```

This separates two possible branch-memory mechanisms:

- the semisimple factor \(\exp(2\pi i\lambda K)\);
- the unipotent factor \(\exp(2\pi iNK)\).

The current case analysis predicts:

| spectral component | predicted behavior |
|---|---|
| \(\lambda\notin\mathbb Q\), arbitrary Jordan structure | injective |
| rational \(\lambda\), one block of size \(1\) | noninjective |
| rational \(\lambda\), one block of size at least \(2\) | injective |
| rational \(\lambda\), two or more Jordan blocks | noninjective |

The global theorem should follow only after these local statements are proved and recombined without hidden assumptions.

## Research discipline

This project uses a strict definition of "new."

Nothing is to be described as new merely because:

- it was not immediately found by search;
- it is phrased differently from a known theorem;
- Lean proves it;
- it combines known lemmas in a pleasing way.

A novelty claim requires a separate bibliographic audit after the mathematics is stable.

## Directory target

Recommended Lean layout:

```text
Semisimple Rational Obstruction Conjecture/
├── README.md
├── Semisimple Rational Obstruction Conjecture - Sources.md
├── Semisimple Rational Obstruction Conjecture - Research Agenda.md
├── Semisimple Rational Obstruction Conjecture - Goal Prompt.md
├── Semisimple Rational Obstruction Conjecture - Checklist.md
├── Semisimple Rational Obstruction Conjecture - Architecture.md
└── SemisimpleRationalObstruction/
    ├── Basic.lean
    ├── MatrixLogFiber.lean
    ├── Counterexample4x4.lean
    ├── BranchOperator.lean
    ├── LocalNonrational.lean
    ├── LocalRationalSingleJordan.lean
    ├── LocalRationalMultipleJordan.lean
    ├── GlobalAssembly.lean
    ├── Main.lean
    └── Audit.lean
```

The Markdown package defines the campaign. The Lean directory is to be created by the agent as the proof architecture stabilizes.
