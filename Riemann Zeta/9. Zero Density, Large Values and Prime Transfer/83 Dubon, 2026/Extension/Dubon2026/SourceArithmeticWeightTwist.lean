import Dubon2026.SourceGaloisCharacterTwist
import Dubon2026.SourceOriginalCyclotomicLocal

/-! DUB-17/18 -> residual Galois association -> the exact weight twist.
The original arithmetic cyclotomic character restores the factor removed
by weight-two descent, on the same arithmetic group and local embedding.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

variable {F : Type} [Field F] [TopologicalSpace F]
  (p : ℕ) [NeZero p] [CharP F p] (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a)

/-- The original arithmetic cyclotomic character with unit values in the
actual residual coefficient field. -/
def sourceArithmeticCyclotomicUnitCharacter :
    rationalArithmeticGaloisGroup a →ₜ* Fˣ where
  toMonoidHom := (Units.map (ZMod.castHom (dvd_refl p) F).toMonoidHom).comp
    (rationalArithmeticCyclotomicCharacter a p hpa).toMonoidHom
  continuous_toFun := (show Continuous
    (Units.map (ZMod.castHom (dvd_refl p) F).toMonoidHom) from
      continuous_of_discreteTopology).comp
        (rationalArithmeticCyclotomicCharacter a p hpa).continuous

/-- At the original residue Frobenius, the unit character has the exact
rational-prime scalar value. -/
theorem sourceArithmeticCyclotomicUnitCharacter_frobenius
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure ell hell)), g • x = x ^ ell) :
    (sourceArithmeticCyclotomicUnitCharacter (F := F) p a hpa
      (rationalPrimeArithmeticRestriction a ell hell g) : F) = (ell : F) := by
  have he : ¬ell ∣ p := fun h => hellp ((Nat.prime_dvd_prime_iff_eq hell hp).mp h)
  change ZMod.castHom (dvd_refl p) F
    (rationalArithmeticCyclotomicCharacter a p hpa
      (rationalPrimeArithmeticRestriction a ell hell g) : ZMod p) = _
  rw [sourceArithmeticCyclotomic_frobenius a p hpa ell hell he g hg,
    ZMod.coe_unitOfCoprime, map_natCast]

/-- The actual residual unit character kills original norm inertia away
from its coefficient characteristic. -/
theorem sourceArithmeticCyclotomicUnitCharacter_inertia
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : g ∈ rationalPrimeNormInertia ell hell) :
    sourceArithmeticCyclotomicUnitCharacter (F := F) p a hpa
      (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  have he : ¬ell ∣ p := fun h => hellp ((Nat.prime_dvd_prime_iff_eq hell hp).mp h)
  change Units.map (ZMod.castHom (dvd_refl p) F).toMonoidHom
    (rationalArithmeticCyclotomicCharacter a p hpa
      (rationalPrimeArithmeticRestriction a ell hell g)) = 1
  rw [sourceArithmeticCyclotomic_inertia a p hpa ell hell he g hg, map_one]

/-- The literal cyclotomic weight twist on the original arithmetic group. -/
def sourceArithmeticWeightTwist (j : ℕ)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F :=
  sourceGaloisCharacterTwist ρ
    ((sourceArithmeticCyclotomicUnitCharacter p a hpa).toMonoidHom ^ j)

/-- The weight twist preserves the original representation's continuity. -/
theorem sourceArithmeticWeightTwist_continuous [IsTopologicalRing F] (j : ℕ)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hρ : Continuous ρ) : Continuous (sourceArithmeticWeightTwist p a hpa j ρ) := by
  apply sourceGaloisCharacterTwist_continuous ρ _ hρ
  exact (sourceArithmeticCyclotomicUnitCharacter p a hpa).continuous.pow j

/-- The exact original Frobenius trace acquires the prescribed weight factor. -/
theorem sourceArithmeticWeightTwist_frobenius_trace (j : ℕ)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure ell hell)), g • x = x ^ ell) :
    Matrix.trace (sourceArithmeticWeightTwist p a hpa j ρ
      (rationalPrimeArithmeticRestriction a ell hell g)).val =
      (ell : F) ^ j *
        Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell hell g)).val := by
  rw [sourceArithmeticWeightTwist, sourceGaloisCharacterTwist_trace]
  change (sourceArithmeticCyclotomicUnitCharacter (F := F) p a hpa
    (rationalPrimeArithmeticRestriction a ell hell g) : F) ^ j * _ = _
  rw [sourceArithmeticCyclotomicUnitCharacter_frobenius p a hpa hp ell hell hellp g hg]

/-- The exact original Frobenius determinant acquires twice the weight exponent. -/
theorem sourceArithmeticWeightTwist_frobenius_det (j : ℕ)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : ∀ x : IsLocalRing.ResidueField
      (algebraicLocalIntegerRing (rationalPrimeLocalClosure ell hell)), g • x = x ^ ell) :
    Matrix.det (sourceArithmeticWeightTwist p a hpa j ρ
      (rationalPrimeArithmeticRestriction a ell hell g)).val =
      (ell : F) ^ (2 * j) *
        Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell hell g)).val := by
  rw [sourceArithmeticWeightTwist, sourceGaloisCharacterTwist_det]
  change ((sourceArithmeticCyclotomicUnitCharacter (F := F) p a hpa
    (rationalPrimeArithmeticRestriction a ell hell g) : F) ^ j) ^ 2 * _ = _
  rw [sourceArithmeticCyclotomicUnitCharacter_frobenius p a hpa hp ell hell hellp g hg,
    ← pow_mul, Nat.mul_comm j 2]

/-- The exact weight twist preserves original inertia triviality away
from the characteristic, with no new ramification condition. -/
theorem sourceArithmeticWeightTwist_inertia (j : ℕ)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hp : p.Prime) (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ p)
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : g ∈ rationalPrimeNormInertia ell hell)
    (hρ : ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1) :
    sourceArithmeticWeightTwist p a hpa j ρ
      (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  apply sourceGaloisCharacterTwist_eq_one _ _ _ hρ
  change (sourceArithmeticCyclotomicUnitCharacter p a hpa
    (rationalPrimeArithmeticRestriction a ell hell g)) ^ j = 1
  rw [sourceArithmeticCyclotomicUnitCharacter_inertia p a hpa hp ell hell hellp g hg, one_pow]

end
end Dubon2026
