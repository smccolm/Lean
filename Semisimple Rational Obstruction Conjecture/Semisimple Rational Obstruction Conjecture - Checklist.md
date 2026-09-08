# Semisimple Rational Obstruction Conjecture - Checklist

Use this as the acceptance contract.

Do not mark an item complete because an informal proof exists. Mark it complete only when the corresponding Lean theorem builds without `sorry`, unless the item is explicitly bibliographic.

## A. Repository and definitions

- [ ] Project builds before new work.
- [ ] Matrix index type and coefficient field are fixed consistently.
- [ ] `IsMatrixLog A L` defined by `Matrix.exp L = A`.
- [ ] `MatrixLogFiber A` defined.
- [ ] `selfPowerFiberMap A L = Matrix.exp (A * L)` defined.
- [ ] Main injectivity predicate defined without principal-logarithm assumptions.
- [ ] Definitions are not tied to the motivating \(3\times3\) matrix.

## B. False original conjecture: permanent counterexample

For

```math
A=J_2(1)\oplus J_2(1),
```

with the explicit \(X,U,Y\) construction:

- [ ] \(N^2=0\).
- [ ] \(U\) invertible.
- [ ] \(UA=AU\).
- [ ] \(Y=UXU^{-1}\).
- [ ] \(X\ne Y\).
- [ ] \(\exp(X)=A\).
- [ ] \(\exp(Y)=A\).
- [ ] \(\exp(AX)=\exp(AY)\).
- [ ] \(\ker(A-I)=\operatorname{im}(A-I)\).
- [ ] Counterexample theorem explicitly states noninjectivity.
- [ ] README records that the original criterion is false.

## C. Centralizer-gap lemma

- [ ] Define matrix centralizer predicate or reuse Mathlib equivalent.
- [ ] Prove conjugation preserves logarithm status when \(U\) commutes with \(A\).
- [ ] Prove conjugation preserves self-power output when \(U\) also commutes with \(\exp(AX)\).
- [ ] Prove \(UX\ne XU\) gives \(UXU^{-1}\ne X\).
- [ ] Package the centralizer-gap noninjectivity lemma.

## D. Branch-operator reduction

- [ ] Choose or construct an appropriate primary logarithm \(L_0\).
- [ ] Prove every matrix logarithm \(L\) commutes with \(A\).
- [ ] Prove \(L\) commutes with \(L_0\).
- [ ] Define
  ```math
  K=(L-L_0)/(2\pi i).
  ```
- [ ] Prove \(\exp(2\pi iK)=I\).
- [ ] Prove admissible \(K\) is diagonalizable.
- [ ] Prove admissible \(K\) has integer spectrum.
- [ ] State the exact converse needed, if any.
- [ ] Do not silently assume every commuting integer-spectrum semisimple \(K\) is admissible unless proved.
- [ ] Prove
  ```math
  \Phi_A(L)=\exp(AL_0)\exp(2\pi iAK).
  ```
- [ ] Reduce injectivity of \(\Phi_A\) to the corresponding branch-operator map.

## E. Local spectral factorization

On a generalized eigenspace:

- [ ] Write \(A=\lambda I+N\) with \(N\) nilpotent.
- [ ] Prove admissible \(K\) preserves the component.
- [ ] Prove \(KN=NK\).
- [ ] Prove
  ```math
  \exp(2\pi iAK)
  =
  \exp(2\pi i\lambda K)\exp(2\pi iNK).
  ```
- [ ] Identify the first factor as semisimple.
- [ ] Identify the second factor as unipotent.
- [ ] Ensure the argument does not assume a basis where none is justified.

## F. Nonrational eigenvalue case

- [ ] Prove for \(\lambda\notin\mathbb Q\):
  ```math
  \exp(2\pi i\lambda k)=\exp(2\pi i\lambda j)
  \Rightarrow k=j
  ```
  for integers \(j,k\).
- [ ] Cover irrational real \(\lambda\).
- [ ] Cover nonreal \(\lambda\).
- [ ] Lift scalar injectivity to diagonalizable integer-spectrum branch operators.
- [ ] Prove local injectivity for arbitrary Jordan multiplicity at nonrational \(\lambda\).
- [ ] Test repeated irrational Jordan blocks explicitly.
- [ ] Test repeated complex Jordan blocks explicitly.

## G. Rational, single Jordan block

For rational nonzero \(\lambda\) and a single Jordan block:

- [ ] Prove centralizer is polynomial in the Jordan nilpotent.
- [ ] Prove a diagonalizable matrix in that polynomial centralizer is scalar.
- [ ] Deduce admissible branch operator has form \(K=kI\).
- [ ] For block size \(1\), construct distinct \(k,j\) with equal output.
- [ ] For block size at least \(2\), prove equality of outputs implies \(k=j\).
- [ ] Formalize `exp(cN) = I -> c = 0` for the required nonzero nilpotent Jordan block.
- [ ] Avoid claiming this for arbitrary nilpotent \(N\) without the needed hypotheses.

## H. Rational, multiple Jordan blocks

- [ ] Handle two blocks of arbitrary positive sizes.
- [ ] Construct nonzero inter-block map \(T\).
- [ ] Prove required relations such as \(N_rT=0\) and \(TN_s=0\).
- [ ] Construct shear \(U\).
- [ ] Prove \(U\) commutes with \(A\).
- [ ] Construct distinct admissible branch operators \(K_0,K_1\).
- [ ] Prove \(K_1=UK_0U^{-1}\).
- [ ] Prove their self-power outputs are equal.
- [ ] Generalize to at least two blocks among any number of blocks.
- [ ] Cover unequal block sizes.

## I. Global assembly

- [ ] Decompose into generalized eigenspaces.
- [ ] Prove logarithms preserve each generalized eigenspace.
- [ ] Prove branch operators preserve each generalized eigenspace.
- [ ] Prove equality of global outputs restricts to equality on each component.
- [ ] Prove noninjectivity on one component lifts to global noninjectivity.
- [ ] Assemble necessity.
- [ ] Assemble sufficiency.
- [ ] Main theorem has no basis-dependent Jordan notation in its public statement.
- [ ] Provide equivalent Jordan-form corollary.

## J. Adversarial tests before acceptance

Try to construct counterexamples using:

- [ ] two repeated irrational blocks;
- [ ] two repeated nonreal blocks;
- [ ] rational blocks of sizes \(2\) and \(3\);
- [ ] three rational blocks;
- [ ] two distinct rational eigenvalues;
- [ ] rational plus irrational spectrum;
- [ ] rational plus nonreal spectrum;
- [ ] nonprimary logarithms with nontrivial commuting similarities;
- [ ] alternate choice of primary logarithm \(L_0\);
- [ ] matrices similar to, but not literally in, Jordan form.

Every failed candidate counterexample should either become a Lean lemma or be documented in `Audit.lean` if it exposes a reusable fact.

## K. Build quality

- [ ] `lake build` succeeds.
- [ ] No `sorry`.
- [ ] No `admit`.
- [ ] No axioms added to force matrix-logarithm classification.
- [ ] No floating-point arguments in theorem proofs.
- [ ] No unused giant generalization layer.
- [ ] Imports are controlled.
- [ ] Public theorem names are stable and descriptive.
- [ ] The explicit \(4\times4\) counterexample remains executable after refactors.

## L. Mathematical write-up

- [ ] Candidate theorem stated exactly.
- [ ] Original false conjecture stated and falsified.
- [ ] Centralizer-gap mechanism explained.
- [ ] Branch-operator reduction explained.
- [ ] Four local cases explained.
- [ ] Global assembly explained.
- [ ] All assumptions are visible.
- [ ] Singular matrices are explicitly out of scope for the main theorem.
- [ ] No novelty language before novelty audit.

## M. Novelty audit

Only after the Lean theorem is complete:

- [ ] Search exact theorem statement.
- [ ] Search equivalent Jordan statement.
- [ ] Search \(\Phi_A(L)=\exp(AL)\) with \(\exp L=A\).
- [ ] Search injectivity of matrix-logarithm fibres.
- [ ] Search Gantmacher references backward.
- [ ] Search Higham citations forward.
- [ ] Search matrix-matrix exponentiation citations forward.
- [ ] Search matrix unwinding citations forward.
- [ ] Search Lambert \(W\) matrix-solution literature for equivalent fibre arguments.
- [ ] Record all close prior results.
- [ ] Decide whether the final theorem is:
  - [ ] already known;
  - [ ] immediate known corollary;
  - [ ] apparently unstated but routine;
  - [ ] plausibly new and nontrivial.
- [ ] Use "new" only if the last category survives serious review.
