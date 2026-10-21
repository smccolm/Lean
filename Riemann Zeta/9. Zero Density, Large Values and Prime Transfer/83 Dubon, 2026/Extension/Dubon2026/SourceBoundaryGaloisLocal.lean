import Dubon2026.SourceBoundaryGaloisRepresentation

/-! DUB-17/18 -> residual Galois association -> boundary Dirichlet pair.
The actual arithmetic representation has the prescribed trace and
determinant at every original residue Frobenius and kills the original
norm inertia away from the level and coefficient characteristic.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

variable {F : Type} [Field F] (N p : ℕ) [CharP F p] [NeZero N] [NeZero p]
  (a : 𝓞 ℚ) (hNa : (N : 𝓞 ℚ) ∣ a) (hpa : (p : 𝓞 ℚ) ∣ a)
  (ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ)

/-- The actual boundary representation has the prescribed Dirichlet trace
at every original residue Frobenius away from the conductor and characteristic. -/
theorem sourceBoundaryGalois_frobenius_trace
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellN : ¬ell ∣ N) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure ell hell)), g • x = x ^ ell) :
    Matrix.trace (sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂
      (rationalPrimeArithmeticRestriction a ell hell g)).val =
      (ψ₁ (ZMod.unitOfCoprime ell (hell.coprime_iff_not_dvd.mpr hellN)) : F) +
        (ell : F) * (ψ₂ (ZMod.unitOfCoprime ell (hell.coprime_iff_not_dvd.mpr hellN)) : F) := by
  have he : ¬ell ∣ p := fun h => hellp ((Nat.prime_dvd_prime_iff_eq hell hp).mp h)
  rw [sourceBoundaryGaloisRepresentation_trace,
    sourceArithmeticCyclotomic_frobenius a N hNa ell hell hellN g hg,
    sourceArithmeticCyclotomic_frobenius a p hpa ell hell he g hg,
    ZMod.coe_unitOfCoprime, map_natCast]

/-- The product-one condition derived from the actual boundary gives
the correct weight-two determinant at the same original Frobenius. -/
theorem sourceBoundaryGalois_frobenius_det
    (hψ : ∀ u, (ψ₁ u : F) * (ψ₂ u : F) = 1)
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure ell hell)), g • x = x ^ ell) :
    Matrix.det (sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂
      (rationalPrimeArithmeticRestriction a ell hell g)).val = (ell : F) := by
  have he : ¬ell ∣ p := fun h => hellp ((Nat.prime_dvd_prime_iff_eq hell hp).mp h)
  rw [sourceBoundaryGaloisRepresentation_det N p a hNa hpa ψ₁ ψ₂ hψ,
    sourceArithmeticCyclotomic_frobenius a p hpa ell hell he g hg,
    ZMod.coe_unitOfCoprime, map_natCast]

/-- The constructed representation kills the original inertia at every
rational prime away from the level and coefficient characteristic. -/
theorem sourceBoundaryGalois_inertia
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellN : ¬ell ∣ N) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : g ∈ rationalPrimeNormInertia ell hell) :
    sourceBoundaryGaloisRepresentation N p a hNa hpa ψ₁ ψ₂
      (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  have he : ¬ell ∣ p := fun h => hellp ((Nat.prime_dvd_prime_iff_eq hell hp).mp h)
  change sourceBoundaryGaloisFiniteRepresentation N p ψ₁ ψ₂
    (rationalArithmeticCyclotomicCharacter a N hNa (rationalPrimeArithmeticRestriction a ell hell g),
      rationalArithmeticCyclotomicCharacter a p hpa (rationalPrimeArithmeticRestriction a ell hell g)) = 1
  rw [sourceArithmeticCyclotomic_inertia a N hNa ell hell hellN g hg,
    sourceArithmeticCyclotomic_inertia a p hpa ell hell he g hg]
  exact map_one _

end
end Dubon2026
