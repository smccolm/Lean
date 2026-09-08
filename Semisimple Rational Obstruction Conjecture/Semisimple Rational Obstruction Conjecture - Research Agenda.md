# Semisimple Rational Obstruction Conjecture - Research Agenda

Status: finite research agenda.

The project is deliberately narrow. It is not a request to classify all multivalued matrix exponentials or all logarithm fibres.

## 1. Research question

For a nonsingular complex matrix \(A\), define

```math
\mathrm{Log}(A)=\{L:\exp(L)=A\}
```

and

```math
\Phi_A(L)=\exp(AL).
```

Determine whether the following repaired criterion is correct:

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

The objective is either:

1. a Lean-checked proof of this criterion; or
2. a Lean-checked counterexample and the smallest defensible repair.

A counterexample is a successful research outcome.

## 2. Known falsification that must be formalized first

The original criterion omitted the condition

```math
\dim\ker(A-\lambda I)=1.
```

Its falsification is part of the permanent record.

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

Let

```math
X=
\begin{bmatrix}
N&0\\
0&N+2\pi iI_2
\end{bmatrix},
```

and

```math
U=
\begin{bmatrix}
I_2&N\\
0&I_2
\end{bmatrix},
\qquad
Y=UXU^{-1}.
```

Formalize:

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

and

```math
\ker(A-I)=\operatorname{im}(A-I).
```

This blocks accidental resurrection of the false conjecture.

## 3. Main proof strategy

### Gate A. Define the logarithm fibre and self-power fibre map

Create definitions close to:

```lean
def IsMatrixLog (A L : Matrix n n ℂ) : Prop :=
  Matrix.exp L = A

def MatrixLogFiber (A : Matrix n n ℂ) : Set (Matrix n n ℂ) :=
  {L | IsMatrixLog A L}

def selfPowerFiberMap (A L : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.exp (A * L)
```

Keep the theorem statement independent of any principal matrix logarithm.

### Gate B. Branch-operator reduction

Fix a primary logarithm \(L_0\).

For any logarithm \(L\), define

```math
K=\frac{L-L_0}{2\pi i}.
```

Prove the exact properties required for the project:

```math
KA=AK,
```

```math
\exp(2\pi iK)=I,
```

and consequently, over \(\mathbb C\),

```math
K\text{ is diagonalizable with integer spectrum}.
```

Then prove

```math
\Phi_A(L)
=
\exp(AL_0)\exp(2\pi iAK).
```

Reduce injectivity of \(\Phi_A\) to injectivity of

```math
\Psi_A(K)=\exp(2\pi iAK)
```

on admissible branch operators.

Do not assume the converse parametrization without proof. If the all-logarithms theorem needed for the converse is absent from Mathlib, either formalize the exact finite-dimensional statement needed or structure the main theorem so that only the necessary direction is imported.

### Gate C. Local generalized-eigenspace analysis

For a generalized eigenspace at eigenvalue \(\lambda\), write

```math
A=\lambda I+N
```

with \(N\) nilpotent.

For admissible \(K\) commuting with \(A\), prove

```math
\Psi_A(K)
=
\exp(2\pi i\lambda K)
\exp(2\pi iNK).
```

The factors commute.

#### Case C1. \(\lambda\notin\mathbb Q\)

Prove that

```math
k\mapsto\exp(2\pi i\lambda k)
```

is injective on integers.

Use this to recover the integer-spectrum branch operator \(K\) from the semisimple factor.

The proof must cover:

- irrational real \(\lambda\);
- nonreal \(\lambda\).

#### Case C2. Rational \(\lambda\), exactly one Jordan block of size at least \(2\)

Prove that the centralizer on this component is the polynomial algebra in the nilpotent Jordan block.

Then prove that an admissible diagonalizable integer-spectrum \(K\) commuting with a single Jordan block must be scalar:

```math
K=kI.
```

Finally prove

```math
\exp(2\pi ik(\lambda I+N))
=
\exp(2\pi ij(\lambda I+N))
```

implies

```math
k=j.
```

The nilpotent factor must carry the branch information when scalar periodicity loses it.

#### Case C3. Rational \(\lambda\), one block of size \(1\)

Construct distinct branch operators producing equal self-power values.

This is the scalar periodicity obstruction.

#### Case C4. Rational \(\lambda\), multiple Jordan blocks

Formalize a general centralizer-gap construction.

Choose a nonzero inter-block map \(T\) satisfying the appropriate intertwining annihilation relations. Construct a unipotent shear

```math
U=
\begin{bmatrix}
I&T\\
0&I
\end{bmatrix}.
```

Construct distinct admissible \(K_0,K_1\) with

```math
K_1=UK_0U^{-1}
```

such that

```math
\Psi_A(K_0)=\Psi_A(K_1).
```

This proves noninjectivity for every rational eigenvalue represented by at least two Jordan blocks.

### Gate D. Global assembly

Prove that logarithms and admissible branch operators preserve generalized eigenspaces.

Show that equality of the global self-power outputs is equivalent to equality on each generalized eigenspace.

Assemble the four local cases into the global iff statement.

This is the main theorem gate.

## 4. Adversarial falsification tasks

Before declaring the main theorem proved, actively search for failures in:

1. repeated irrational eigenvalues;
2. repeated nonreal eigenvalues;
3. unequal Jordan block sizes;
4. three or more blocks at one rational eigenvalue;
5. distinct rational eigenvalues with arithmetic relations;
6. rational and irrational components together;
7. matrices with nontrivial nilpotent parts on nonrational eigenvalues;
8. logarithms not represented by an initially convenient branch parametrization;
9. nonprimary logarithms generated by arbitrary allowed centralizer conjugations;
10. any dependence on choice of primary logarithm \(L_0\).

If a counterexample appears, formalize it before repairing the statement.

## 5. Secondary theorem targets

These are acceptable only after the main theorem architecture is stable.

### Centralizer-gap lemma

For \(X\in\mathrm{Log}(A)\), if an invertible \(U\) satisfies

```math
UA=AU,
```

```math
U\exp(AX)=\exp(AX)U,
```

but

```math
UX\ne XU,
```

then with

```math
Y=UXU^{-1}
```

one has

```math
Y\ne X,
\qquad
\exp(Y)=A,
\qquad
\exp(AY)=\exp(AX).
```

This is a reusable mechanism for constructing noninjectivity.

### Minimal \(4\times4\) counterexample

Prove the explicit \(J_2(1)\oplus J_2(1)\) example.

If practical, separately prove a dimension-minimality statement for this specific hidden derogatory obstruction. Do not spend substantial effort on minimality unless it falls naturally from the Jordan analysis.

## 6. What not to do

Do not:

- classify every fibre of \(\Phi_A\);
- classify all possible orbit closures;
- develop general Riemann-surface machinery;
- formalize a full general matrix logarithm library unless forced by the target;
- chase numerical conditioning;
- generalize to arbitrary matrix-matrix exponentiation \(A^B\);
- pursue singular matrices or the \(0^0\) regularization in the first campaign;
- claim novelty before the separate novelty audit.

Those are token furnaces.

## 7. Acceptance state

The campaign is complete when one of the following holds.

### Proof outcome

- explicit false-conjecture counterexample formalized;
- branch-operator reduction formalized;
- all four local cases formalized;
- global repaired criterion formalized;
- no `sorry`;
- full project builds;
- theorem statement is basis-independent;
- paper proof extracted from the Lean dependency graph;
- novelty audit completed separately.

### Counterexample outcome

- repaired criterion falsified by a concrete exact matrix;
- counterexample formalized in Lean;
- failed proof gate identified precisely;
- smallest defensible repair stated;
- no unsupported novelty language.

Either outcome is research progress.
