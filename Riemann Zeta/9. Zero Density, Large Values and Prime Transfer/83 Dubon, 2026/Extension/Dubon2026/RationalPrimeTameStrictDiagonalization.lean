import Dubon2026.RationalPrimePrescribedFrobeniusMatrices
import Dubon2026.TameStrictDiagonalization

/-! # Actual auxiliary-prime tame deformations in a strict diagonal basis

This consumer keeps the original finite field, embedding, restriction,
representation and prescribed Frobenius. It constructs the tame generator
and common basis used by the local deformation rings on the path to
Dubon Theorem 2.6; arithmetic ring realization remains a separate obligation.
-/

namespace Dubon2026
open Matrix IsLocalRing

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- At the same original prime and specified arithmetic Frobenius, an actual
residual-unramified Artinian deformation with distinct diagonal residual
Frobenius eigenvalues admits the required simultaneous strict diagonal form.
Its inertia generator, wild-kernel removal and diagonalizing basis are derived. -/
theorem rationalPrime_artinian_tame_strict_diagonalization
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {F A ι : Type} [Field F] [NumberField F]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Fintype ι] [DecidableEq ι] [CharP (ResidueField A) q]
    (hpone : (p : ResidueField A) = 1)
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hφ : ∀ x : ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure p hp)), φ • x = x ^ p)
    (ρ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      GeneralLinearGroup ι A)
    (hres : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (residue A) (ρ g) = 1)
    (α : ι → ResidueField A) (hα : Function.Injective α)
    (hF : (ρ (QuotientGroup.mk' r.ker φ)).val.map (residue A) = diagonal α) :
    ∃ (t : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker)
      (U : GeneralLinearGroup ι A) (l b : ι → A),
      t ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker) ∧
      ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)).map ρ =
        Subgroup.zpowers (ρ t) ∧
      GeneralLinearGroup.map (residue A) U = 1 ∧
      (MulAut.conj U⁻¹ (ρ (QuotientGroup.mk' r.ker φ))).val = diagonal l ∧
      (MulAut.conj U⁻¹ (ρ t)).val = diagonal b ∧
      (∀ i, residue A (l i) = α i) ∧
      (∀ i, residue A (b i) = 1) ∧
      (∀ i, IsUnit (l i)) ∧ (∀ i, IsUnit (b i)) ∧
      ∀ i, (b i) ^ p = b i := by
  obtain ⟨t, ht, himage, hrel⟩ :=
    rationalPrime_artinian_tame_matrices_at_frobenius p q hp hq hpq e r he φ hφ ρ hres
  obtain ⟨U, l, b, hdiag⟩ := regularResidue_tame_strict_diagonalization
    (ρ (QuotientGroup.mk' r.ker φ)) (ρ t) α hF hα (hres t ht) p hpone hrel
  exact ⟨t, U, l, b, ht, himage, hdiag⟩

end Dubon2026
