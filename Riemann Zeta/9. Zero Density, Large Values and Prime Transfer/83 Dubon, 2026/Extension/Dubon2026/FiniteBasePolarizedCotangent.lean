import Dubon2026.FiniteBasePolarizedCoefficientRing
import Dubon2026.PolarizedCotangentDimension

/-! The actual finite-base arithmetic ring consumes its derived residual
generators to obtain the full-adjoint cotangent classification and dimension
on the DUB-17 source deformation chain. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Use the original rational algebra for the actual coefficient-ring base group. -/
local instance finiteBasePolarizedCotangentUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
  (σ : finiteBaseArithmeticGaloisGroup a F →ₜ*
    PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)

variable [Nonempty ι] [CharP (IsLocalRing.ResidueField O) p]
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The actual arithmetic polarized cotangent dual is the original continuous full-adjoint cocycle module, with no supplied generator or comparison certificate. -/
def finiteBasePolarizedCotangentCocycleLinearEquiv :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     OriginalRelativeMaximalCotangentDual
       (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν hν) ≃ₗ[IsLocalRing.ResidueField O]
       continuousRepresentationCocyclesOne (polarizedAdjointRep σ.toMonoidHom)) :=
  fixedResidualPolarizedMaximalCotangentCocycleLinearEquiv p hp
    (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

include ha hp hpa hν in
/-- The actual arithmetic polarized coefficient ring proves finite-dimensionality of the original continuous full-adjoint cocycles. -/
theorem finiteBasePolarizedCocycles_finite :
    Module.Finite (IsLocalRing.ResidueField O)
      (continuousRepresentationCocyclesOne (polarizedAdjointRep σ.toMonoidHom)) :=
  fixedResidualPolarizedCocycles_finite p hp (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

/-- The actual finite-base arithmetic cotangent quotient has the original full-adjoint framed tangent dimension. -/
theorem finiteBasePolarizedCotangent_finrank_add_invariants :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     letI := originalMaximalCotangentResidueModule
       (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν hν)
     Module.finrank (IsLocalRing.ResidueField O)
       (RelativeMaximalCotangent O (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν)) +
       Module.finrank (IsLocalRing.ResidueField O)
         (Representation.invariants (polarizedAdjointRepresentation.comp σ.toMonoidHom)) =
       Module.finrank (IsLocalRing.ResidueField O)
         (ContinuousRepresentationH1 (polarizedAdjointRep σ.toMonoidHom)
           (polarizedAdjointAction_continuous σ.toMonoidHom σ.continuous)) + Fintype.card ι ^ 2) :=
  fixedResidualPolarizedCotangent_finrank_add_invariants p hp
    (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

end
end Dubon2026

