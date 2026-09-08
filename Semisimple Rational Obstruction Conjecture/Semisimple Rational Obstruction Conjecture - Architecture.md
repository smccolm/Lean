# Semisimple Rational Obstruction Conjecture - Architecture

Status: proposed Lean architecture.

The architecture is intentionally narrow. Every module must be consumed by the main injectivity theorem, its counterexamples, or the audit.

## 1. Dependency spine

```text
Basic
  |
  v
MatrixLogFiber
  |
  +----------------------+
  |                      |
  v                      v
Counterexample4x4    BranchOperator
                         |
                         v
                  Local spectral split
                    /        |        \
                   /         |         \
                  v          v          v
       LocalNonrational   LocalRationalSingleJordan
                                  |
                                  v
                       LocalRationalMultipleJordan
                                  |
                                  v
                           GlobalAssembly
                                  |
                                  v
                                Main
                                  |
                                  v
                                Audit
```

The explicit counterexample is intentionally near the root. It must not depend on the full abstract theory.

## 2. Recommended files

### `SemisimpleRationalObstruction/Basic.lean`

Purpose:

- common imports;
- scalar constants;
- small matrix-exp helper lemmas;
- commuting-exponential helper lemmas;
- exact finite-dimensional algebra needed repeatedly.

Possible contents:

```lean
namespace SemisimpleRationalObstruction
```

Avoid defining a large custom matrix-function framework.

### `SemisimpleRationalObstruction/MatrixLogFiber.lean`

Purpose:

Define the public objects.

Suggested core:

```lean
def IsMatrixLog (A L : Matrix n n ℂ) : Prop :=
  Matrix.exp L = A

def MatrixLogFiber (A : Matrix n n ℂ) : Set (Matrix n n ℂ) :=
  {L | IsMatrixLog A L}

def selfPowerFiberMap (A L : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.exp (A * L)

def SelfPowerFiberInjective (A : Matrix n n ℂ) : Prop :=
  Set.InjOn (selfPowerFiberMap A) (MatrixLogFiber A)
```

If a linear-map formulation is more compatible with Mathlib spectral theory, provide equivalence lemmas rather than duplicating the entire development.

### `SemisimpleRationalObstruction/Counterexample4x4.lean`

Purpose:

Permanent formal falsification of the original conjecture.

Define explicit:

```math
N,\ J,\ A,\ X,\ U,\ Y.
```

Prove:

```math
X\ne Y,
\quad
\exp X=A,
\quad
\exp Y=A,
\quad
\exp(AX)=\exp(AY),
```

and the kernel/image equality.

This file should require as little abstract infrastructure as possible.

Acceptance theorem should be visibly named, for example:

```lean
theorem original_semisimple_rational_obstruction_false : ...
```

The exact theorem statement should expose the mathematical counterexample, not merely return `¬ OldConjecture`.

### `SemisimpleRationalObstruction/BranchOperator.lean`

Purpose:

Convert arbitrary logarithms into branch operators relative to a fixed primary logarithm.

Core conceptual definitions:

```math
K=(L-L_0)/(2\pi i).
```

Target lemmas:

```math
KA=AK,
```

```math
\exp(2\pi iK)=I,
```

```math
\Phi_A(L)=\exp(AL_0)\exp(2\pi iAK).
```

Formalize only the exact all-logarithms machinery consumed later.

Potential intermediate structure:

```lean
structure BranchOperatorData where
  K : Matrix n n ℂ
  commutes : K * A = A * K
  exp_periodic : Matrix.exp ((2 * π * I) • K) = 1
```

Do not commit to a structure unless it reduces proof duplication.

### `SemisimpleRationalObstruction/LocalNonrational.lean`

Purpose:

Prove injectivity on a generalized eigenspace for \(\lambda\notin\mathbb Q\).

Separate the scalar fact from the matrix fact.

Scalar engine:

```math
e^{2\pi i\lambda k}=e^{2\pi i\lambda j}
\Rightarrow k=j.
```

Matrix lift:

For semisimple integer-spectrum branch operators, prove the exponential factor determines the spectral projections of \(K\).

Cover both irrational real and nonreal \(\lambda\).

### `SemisimpleRationalObstruction/LocalRationalSingleJordan.lean`

Purpose:

Handle exactly one Jordan block at rational \(\lambda\).

Split:

#### block size \(1\)

Explicit collision by periodicity.

#### block size at least \(2\)

Show:

1. commuting branch operator lies in the polynomial centralizer;
2. semisimple such operator must be scalar;
3. nilpotent exponential records the scalar branch integer.

A public theorem should distinguish size \(1\) from size at least \(2\).

### `SemisimpleRationalObstruction/LocalRationalMultipleJordan.lean`

Purpose:

Generalize the \(4\times4\) shear mechanism.

Develop only enough block-matrix machinery to construct:

```math
U=
\begin{bmatrix}
I&T\\
0&I
\end{bmatrix}
```

for two chosen blocks and extend it by identity on remaining blocks.

Core theorem:

> If a rational eigenvalue has at least two Jordan blocks, then the self-power fibre map is not injective on that generalized eigenspace.

Use exact inter-block maps.

### `SemisimpleRationalObstruction/GlobalAssembly.lean`

Purpose:

Combine generalized eigenspace results.

Responsibilities:

- spectral/generalized-eigenspace decomposition;
- invariance of components under logarithms;
- restriction of branch operators;
- local-to-global injectivity;
- local counterexample extension to global matrix.

Public theorem should be basis-independent.

Candidate public statement:

```lean
theorem selfPowerFiberInjective_iff_rational_primary_single_chain
    (hA : IsUnit A) :
    SelfPowerFiberInjective A ↔
      ∀ λ, IsEigenvalue A λ → IsRationalComplex λ →
        finrank ℂ (eigenspace A λ) = 1 ∧
        eigenspace A λ ≤ LinearMap.range (A - λ • 1) := ...
```

This is schematic only. Use the actual Mathlib vocabulary available.

### `SemisimpleRationalObstruction/Main.lean`

Purpose:

Stable import surface for the project.

It should expose:

- false original conjecture theorem;
- centralizer-gap lemma;
- repaired main theorem if proved;
- Jordan-form corollary if proved.

No exploratory code.

### `SemisimpleRationalObstruction/Audit.lean`

Purpose:

Adversarial theorem tests and regression cases.

Include concrete matrices for:

- repeated irrational blocks;
- repeated nonreal blocks;
- rational block sizes \(2+3\);
- three rational blocks;
- mixed rational/irrational components;
- mixed rational/nonreal components.

This file should try to instantiate the public theorem on small exact matrices.

It must build.

## 3. Theorem dependency order

Recommended proof order:

```text
T0  Matrix exponential helper lemmas
T1  Definitions of logarithm fibre and Phi_A
T2  Explicit 4x4 false-conjecture witness
T3  Centralizer-gap lemma
T4  Logarithms commute with A
T5  Branch-operator periodicity
T6  Integer-spectrum semisimplicity from exp(2 pi i K)=I
T7  Local split exp(2 pi i A K)
T8  Nonrational scalar injectivity
T9  Nonrational local injectivity
T10 Single-Jordan centralizer
T11 Rational J1 noninjectivity
T12 Rational J_r, r>=2 injectivity
T13 Multiple-rational-block shear
T14 Multiple-rational-block noninjectivity
T15 Generalized-eigenspace preservation
T16 Local-to-global injectivity
T17 Local-to-global noninjectivity
T18 Main iff theorem
T19 Jordan-form corollary
T20 Audit instances
```

Do not work on `T18` while foundational uncertainty remains in `T4` through `T7`.

## 4. Mathematical invariants to preserve

The public theorem should not depend on:

- an ordering of eigenvalues;
- an ordering of Jordan blocks;
- eigenvector normalization;
- a chosen Jordan basis;
- a chosen principal logarithm.

Jordan form is proof infrastructure, not the intended public semantics.

## 5. Known dangerous point

The statement

```math
K=(L-L_0)/(2\pi i)
```

must not be treated casually.

The formal development must justify all claims needed about \(K\), especially:

- commutation;
- periodic exponential;
- semisimplicity;
- integer spectrum;
- whether every admissible \(K\) yields a logarithm when added to \(L_0\).

If a full converse is difficult, avoid requiring it in theorem directions where it is unnecessary.

## 6. Counterexample architecture

Counterexamples should be explicit and low-dimensional.

Preferred style:

```lean
def N2 : Matrix (Fin 2) (Fin 2) ℂ := ...
def A4 : Matrix (Fin 4) (Fin 4) ℂ := ...
def X4 : Matrix (Fin 4) (Fin 4) ℂ := ...
def U4 : Matrix (Fin 4) (Fin 4) ℂ := ...
def Y4 : Matrix (Fin 4) (Fin 4) ℂ := ...
```

Then small lemmas:

```lean
theorem N2_sq : N2 * N2 = 0 := ...
theorem exp_N2 : Matrix.exp N2 = 1 + N2 := ...
theorem U4_commutes_A4 : U4 * A4 = A4 * U4 := ...
```

and finally the packaged theorem.

This makes failures easy to diagnose.

## 7. Scope boundary

The first campaign excludes:

- singular \(A\);
- zero eigenvalues;
- continuous regularization of \(0^0\);
- arbitrary \(A^B\);
- infinite-dimensional operators;
- numerical conditioning;
- topology of complete branch orbits;
- full classification of \(\mathrm{Log}(A)\) as a standalone deliverable.

Only add infrastructure outside this boundary when the main theorem consumes it directly.
