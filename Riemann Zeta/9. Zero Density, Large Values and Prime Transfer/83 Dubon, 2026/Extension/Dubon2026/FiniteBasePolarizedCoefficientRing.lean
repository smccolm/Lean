import Dubon2026.FiniteBasePolarizedPresentation
import Dubon2026.FixedResidualPolarizedResidue

/-! The actual polarized coefficient ring over an original finite arithmetic
base, using its derived residual generators and every original relation.
This consumes the arithmetic presentation on the DUB-17 CM route. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Use the original rational algebra for the actual coefficient-ring base group. -/
local instance finiteBasePolarizedCoefficientUnionAlgebra (a : 𝓞 ℚ) :
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

/-- The actual polarized quotient with the arithmetic finite generators already derived. -/
abbrev FiniteBasePolarizedCoefficientRing :=
  FixedResidualPolarizedCoefficientRing p (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν

variable (hν : ∀ g, polarizedSimilitude (σ g) =
  Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

include hν in
/-- The original arithmetic polarized coefficient quotient is local. -/
theorem finiteBasePolarizedCoefficientRing_isLocal :
    IsLocalRing (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν) :=
  fixedResidualPolarizedCoefficientRing_isLocal p (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

/-- Arithmetic finite generation gives the actual complete local Noetherian
polarized ring in its original maximal-adic quotient topology. -/
theorem finiteBasePolarizedCoefficientRing_localData :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     IsNoetherianRing (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν) ∧
       IsAdic (IsLocalRing.maximalIdeal (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν)) ∧
       IsAdicComplete (IsLocalRing.maximalIdeal (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν))
         (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν)) :=
  fixedResidualPolarizedCoefficientRing_localData p (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

/-- The same arithmetic quotient retains the original coefficient residue field. -/
def finiteBasePolarizedCoefficientResidueEquiv :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     IsLocalRing.ResidueField (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν) ≃ₐ[O]
       IsLocalRing.ResidueField O) :=
  fixedResidualPolarizedCoefficientResidueEquiv p (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
    (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

end
end Dubon2026
