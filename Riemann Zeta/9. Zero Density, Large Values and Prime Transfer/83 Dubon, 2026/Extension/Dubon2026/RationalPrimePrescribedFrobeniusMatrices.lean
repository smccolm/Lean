import Dubon2026.RationalPrimeArtinianTameMatrices

/-! # Tame matrix equations for the same prescribed original Frobenius

The auxiliary local-ring computation for Dubon Theorem 2.6 must retain the
Frobenius whose residual eigenvalues were selected. The original finite tame
generator proof works for that prescribed arithmetic Frobenius directly.
-/

namespace Dubon2026
open Matrix

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The same specified original arithmetic Frobenius admits an actual tame
inertia generator whose image satisfies the matrix relation in the original
Artinian deformation. Wild inertia is constructed and killed internally. -/
theorem rationalPrime_artinian_tame_matrices_at_frobenius
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {F A ι : Type} [Field F] [NumberField F]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Fintype ι] [DecidableEq ι] [CharP (IsLocalRing.ResidueField A) q]
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (hφ : ∀ x : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure p hp)), φ • x = x ^ p)
    (ρ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      GeneralLinearGroup ι A)
    (hres : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (IsLocalRing.residue A) (ρ g) = 1) :
    ∃ t : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker,
      t ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker) ∧
      ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)).map ρ =
        Subgroup.zpowers (ρ t) ∧
      ρ (QuotientGroup.mk' r.ker φ) * ρ t * (ρ (QuotientGroup.mk' r.ker φ))⁻¹ = ρ t ^ p := by
  obtain ⟨t, W, ht, _, hWp, hWle, hgen, hrel⟩ :=
    algebraicLocal_exists_finite_tame_generator e p hp
      (rationalPrimeOriginalClosureNorm_prime_lt_one p hp) r he φ hφ
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hkill := artinian_residual_unramified_kills_wild p q hq hcop
    ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)) W hWle hWp ρ hres
  exact ⟨t, ht, tame_inertia_image_and_frobenius
    ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)) W
    (QuotientGroup.mk' r.ker φ) t p hgen hrel ρ hkill⟩

end Dubon2026
