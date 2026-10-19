import Dubon2026.RationalPrimeFiniteTameGenerator
import Dubon2026.TameArtinianMatrixFactor

/-! At the original rational prime away from the coefficient prime, actual
Artinian deformations with unramified residual inertia have cyclic inertia
image and the Frobenius matrix relation. The wild subgroup is constructed and
then killed using the native residual-kernel p-group theorem. This supplies
necessary equations for the ramified auxiliary local deformation ring in the
arithmetic patching chain to Dubon Theorem 2.6. Representability and the Hecke
comparison remain separate obligations. -/

namespace Dubon2026

open Matrix

theorem rationalPrime_artinian_residual_unramified_tame_matrices
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {F A ι : Type} [Field F] [NumberField F]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [Fintype ι] [DecidableEq ι] [CharP (IsLocalRing.ResidueField A) q]
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (ρ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      GeneralLinearGroup ι A)
    (hres : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (IsLocalRing.residue A) (ρ g) = 1) :
    ∃ (φ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
      (t : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker),
      t ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker) ∧
      ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)).map ρ =
        Subgroup.zpowers (ρ t) ∧
      ρ (QuotientGroup.mk' r.ker φ) * ρ t * (ρ (QuotientGroup.mk' r.ker φ))⁻¹ = ρ t ^ p := by
  obtain ⟨φ, t, W, hW, ht, hWp, hWle, hgen, hrel, _⟩ :=
    rationalPrime_exists_finite_tame_generator p hp e r he
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hkill := artinian_residual_unramified_kills_wild p q hq hcop
    ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)) W hWle hWp ρ hres
  have hmatrix := tame_inertia_image_and_frobenius
    ((rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)) W
    (QuotientGroup.mk' r.ker φ) t p hgen hrel ρ hkill
  exact ⟨φ, t, ht, hmatrix⟩

end Dubon2026
