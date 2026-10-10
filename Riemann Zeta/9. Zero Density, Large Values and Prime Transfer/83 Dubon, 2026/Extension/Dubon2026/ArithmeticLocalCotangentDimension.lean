import Dubon2026.ArithmeticLocalDerivationCocycles
import Dubon2026.ArithmeticLocalCocycleClasses
import Dubon2026.ArithmeticLocalCotangentDual
import Dubon2026.ContinuousAdjointCoboundaryDimension

/-! # The actual arithmetic framed cotangent dimension and original invariant matrices -/

namespace Dubon2026

noncomputable section
open Matrix IsDedekindDomain
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]

/-- The ordinary residue dual of the literal arithmetic relative cotangent quotient is linearly equivalent to the actual local first-order continuous cocycles. -/
def arithmeticLocalCotangentDualCocycleLinearEquiv
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP ≃ₗ[IsLocalRing.ResidueField O]
      arithmeticLocalFirstOrderCocycles a σ P.asIdeal :=
  (arithmeticLocalCotangentDualLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).trans
    ((arithmeticLocalMaximalCotangentLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).trans
      ((arithmeticLocalCotangentDerivationLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).trans
        (arithmeticLocalResidueDerivationLocalCocycleLinearEquiv a ha p hp hpa σ hσ δ hδ P hP)))

/-- The genuine ordinary cotangent dual dimension is the sum of the original local cohomology dimension and the actual change-of-basis coboundary dimension. -/
theorem arithmeticLocalCotangentDual_finrank
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) =
      Module.finrank (IsLocalRing.ResidueField O)
        (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) +
      Module.finrank (IsLocalRing.ResidueField O) (continuousMatrixAdjointCoboundaries σ hσ) := by
  exact (arithmeticLocalCotangentDualCocycleLinearEquiv a ha p hp hpa σ hσ δ hδ P hP).finrank_eq.trans
    (arithmeticLocalFirstOrderCocycles_finrank a ha p hp hpa σ hσ P.asIdeal hP)

/-- The actual framed cotangent dual and original adjoint invariant matrices satisfy the genuine local tangent dimension formula. -/
theorem arithmeticLocalCotangentDual_finrank_add_invariants
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    [CharP (IsLocalRing.ResidueField O) p]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) =
      Units.map (algebraMap O (IsLocalRing.ResidueField O)) (δ g))
    (P : HeightOneSpectrum (𝓞 (rationalUnramifiedExtension a)))
    (hP : rationalArithmeticInertia a P.asIdeal ≤ σ.ker) :
    Module.finrank (IsLocalRing.ResidueField O) (ArithmeticLocalCotangentDual a ha p hp hpa σ hσ δ hδ P hP) +
      Module.finrank (IsLocalRing.ResidueField O) (matrixAdjointRepresentation σ).invariants =
    Module.finrank (IsLocalRing.ResidueField O)
      (arithmeticUnramifiedFixedDeterminantClasses a σ hσ P.asIdeal) + Fintype.card ι ^ 2 := by
  rw [arithmeticLocalCotangentDual_finrank a ha p hp hpa σ hσ δ hδ P hP, add_assoc,
    continuousMatrixAdjointCoboundaries_finrank_add_invariants]

end
end Dubon2026
