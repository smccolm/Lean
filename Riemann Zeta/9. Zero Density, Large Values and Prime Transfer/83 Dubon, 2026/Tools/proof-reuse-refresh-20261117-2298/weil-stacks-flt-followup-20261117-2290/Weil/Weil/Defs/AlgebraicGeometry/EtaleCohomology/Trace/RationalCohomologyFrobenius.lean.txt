module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import Weil.Attr
public import Weil.Definitions

/-!
# The Frobenius endomorphism of the rational ℓ-adic cohomology of a proper scheme

Let `k` be a finite field with `q` elements, `k̄` an algebraic closure of `k`, `ℓ` a prime and
`X` a scheme proper over `k`. Since `X` is proper over `k`, the identity of `X` is a
compactification of `X`, so the compactly supported cohomology of the geometric fibre `X_k̄`
with coefficients in the constant ℓ-adic sheaf `ℤ_ℓ` is the ordinary ℓ-adic cohomology, and

`H^ν(X_k̄, ℚ_ℓ) = H^ν_c(X_k̄, ℤ_ℓ) ⊗_{ℤ_ℓ} ℚ_ℓ`.

The geometric Frobenius `π_X^*` acts on it; this is the Frobenius endomorphism `F_ν`. For
`ℓ ≠ char k` these groups are finite dimensional over `ℚ_ℓ` (the trace formula), and
`P_ν(t) = det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))` is the reverse of the characteristic polynomial of `F_ν`.
The *Weil estimate* `W(X/k)` is the statement that every eigenvalue `λ ∈ ℚ̄_ℓ` of every `F_ν` is
an algebraic number all of whose complex absolute values equal `q ^ (ν / 2)`.

## Main definitions

These are defined in `Weil.Definitions`:

* `Weil.rationalCohomology`: `H^ν(X_k̄, ℚ_ℓ)`.
* `Weil.rationalFrobenius`: the Frobenius endomorphism `F_ν` of `H^ν(X_k̄, ℚ_ℓ)`.
* `Weil.rationalFrobeniusCharpolyReverse`: `P_ν(t) = det(1 - t F_ν)`.
* `Weil.SatisfiesWeilEstimate`: the property `W(X/k)`.

## Main results

* `Weil.finiteDimensional_rationalCohomology`: `H^ν(X_k̄, ℚ_ℓ)` is finite dimensional for
  `ℓ ≠ char k` (the instance is in `Weil.Definitions`).
* `Weil.rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius`: the Frobenius does
  not depend on how `Fintype.card k` is written as a power of the characteristic.

## Implementation notes

The cohomology is Stacks' `rationalGeometricCompactlySupportedCohomology` for the constant
ℓ-adic system `constantSystem`, the compactification `CompactificationOf.ofProper f` and the
algebraic closure `AlgebraicClosure k`; the Frobenius is Stacks' canonical geometric Frobenius
`rationalGeometricCompactlySupportedFrobenius`, with the characteristic `p` and the exponent `e`
of `Fintype.card k = p ^ e` read off from `k`. The degree is a natural number, cast to `ℤ`.
The hypothesis `ℓ ≠ char k` (equivalently `ℓ ∤ q`) enters as an instance `Fact (ℓ ≠ ringChar k)`,
so that the characteristic polynomial can be formed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
* [Stacks] The Stacks Project, Tags 03UT, 03V2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Weil

/-- A scheme proper over a field is noetherian. -/
theorem isNoetherian_of_isProper {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] : IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X :=
    ⟨by simpa using (quasiCompact_iff f).mp inferInstance _ isOpen_univ isCompact_univ⟩
  exact ⟨⟩

/-- A scheme proper over a field is quasi-separated. -/
theorem quasiSeparatedSpace_of_isProper {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] : QuasiSeparatedSpace X :=
  @IsLocallyNoetherian.quasiSeparatedSpace X (isNoetherian_of_isProper f).toIsLocallyNoetherian

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The Frobenius endomorphism is Stacks' geometric Frobenius for every presentation of
`Fintype.card k` as a power `p ^ e` of the characteristic. -/
theorem rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius
    [IsNoetherian X.1] [QuasiSeparatedSpace X.1] (p e : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ e)
    (ν : ℕ) :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f (CompactificationOf.ofProper f)
      (AlgebraicClosure k) p e hcard (LAdicSheaf.constantSystem B X ℓ) ν).hom =
      rationalFrobenius B X f ℓ ν := by
  have hp : p = ringChar k := (ringChar.eq k p).symm
  subst hp
  have he : e = (FiniteField.card k (ringChar k)).choose := by
    apply Nat.pow_right_injective (Fact.out : (ringChar k).Prime).two_le
    exact hcard.symm.trans (FiniteField.card k (ringChar k)).choose_spec.2
  subst he
  rfl

omit [Fintype k] in
/-- `H^ν(X_k̄, ℚ_ℓ)` is finite dimensional over `ℚ_ℓ` when `ℓ ≠ char k` (Tag 03V2). -/
theorem finiteDimensional_rationalCohomology [Finite k] (hℓ : ℓ ≠ ringChar k) (ν : ℕ) :
    FiniteDimensional ℚ_[ℓ] (rationalCohomology B X f ℓ ν) :=
  haveI : Fact (ℓ ≠ ringChar k) := ⟨hℓ⟩
  inferInstance

end Weil
