import Dubon2026.OriginalRelativeCotangentDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Genuine original residue-field dimensions of the relative maximal-ideal quotient -/

namespace Dubon2026

noncomputable section

variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The actual relative maximal-ideal quotient is finite-dimensional over the original coefficient residue field through the genuine original residue identification. -/
theorem originalMaximalCotangent_finite [IsNoetherianRing R]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := originalMaximalCotangentResidueModule eR
     Module.Finite (IsLocalRing.ResidueField O) (RelativeMaximalCotangent O R)) := by
  letI := originalMaximalCotangentResidueModule eR
  letI := (localCoefficientReduction eR).toRingHom.toAlgebra
  letI : Module.Finite R (RelativeMaximalCotangent O R) :=
    Module.Finite.of_surjective (relativeMaximalCotangentMk O R)
      (relativeMaximalCotangentMk_surjective O R)
  letI : IsScalarTower R (IsLocalRing.ResidueField O) (RelativeMaximalCotangent O R) :=
    IsScalarTower.of_algebraMap_smul (originalMaximalCotangent_reduction_smul eR)
  exact Module.Finite.of_restrictScalars_finite R (IsLocalRing.ResidueField O)
    (RelativeMaximalCotangent O R)

/-- The genuine ordinary dual of the relative maximal-ideal quotient is finite-dimensional over the original residue field. -/
theorem originalRelativeMaximalCotangentDual_finite [IsNoetherianRing R]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Module.Finite (IsLocalRing.ResidueField O) (OriginalRelativeMaximalCotangentDual eR) := by
  letI := originalMaximalCotangentResidueModule eR
  letI : Module.Finite (IsLocalRing.ResidueField O) (RelativeMaximalCotangent O R) :=
    originalMaximalCotangent_finite eR
  exact inferInstanceAs (Module.Finite (IsLocalRing.ResidueField O)
    (Module.Dual (IsLocalRing.ResidueField O) (RelativeMaximalCotangent O R)))

/-- The original relative cotangent quotient and its ordinary original residue-field dual have exactly the same dimension. -/
theorem originalRelativeMaximalCotangentDual_finrank
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := originalMaximalCotangentResidueModule eR
     Module.finrank (IsLocalRing.ResidueField O) (OriginalRelativeMaximalCotangentDual eR) =
       Module.finrank (IsLocalRing.ResidueField O) (RelativeMaximalCotangent O R)) := by
  letI := originalMaximalCotangentResidueModule eR
  exact Subspace.dual_finrank_eq

end
end Dubon2026
