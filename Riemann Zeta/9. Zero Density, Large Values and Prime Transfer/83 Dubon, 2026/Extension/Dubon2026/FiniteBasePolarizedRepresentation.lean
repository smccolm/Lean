import Dubon2026.FiniteBasePolarizedCoefficientRing
import Dubon2026.FixedResidualPolarizedContinuity

/-! The genuine continuous universal polarized representation over the
finite-base arithmetic coefficient ring. Its residual comparison and
source characters retain the original arithmetic input for DUB-17. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Use the original rational algebra for the universal arithmetic representation. -/
local instance finiteBasePolarizedRepresentationUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
  (σ : finiteBaseArithmeticGaloisGroup a F →ₜ*
    PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : finiteBaseArithmeticGaloisGroup a F →* Oˣ)
  (hν : ∀ g, polarizedSimilitude (σ g) =
    Units.map (algebraMap O (IsLocalRing.ResidueField O)) (ν g))

/-- The actual original continuous polarized representation over the arithmetic coefficient quotient. -/
@[irreducible] def finiteBasePolarizedUniversalRepresentation :
    finiteBaseArithmeticGaloisGroup a F →ₜ*
      PolarizedGaloisGroup ι (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν) :=
  ⟨fixedResidualPolarizedUniversalRepresentation p (finiteBaseArithmeticGaloisGroup a F) σ.toMonoidHom
      (polarizedBlockRepresentation_continuous.comp σ.continuous)
      (finiteBasePolarizedGenerators a F ha p hp hpa σ)
      (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν,
    fixedResidualPolarizedUniversalRepresentation_continuous p (finiteBaseArithmeticGaloisGroup a F)
      σ.toMonoidHom (polarizedBlockRepresentation_continuous.comp σ.continuous)
      (finiteBasePolarizedGenerators a F ha p hp hpa σ)
      (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν⟩

/-- The same arithmetic universal representation reduces to the entire original polarized residual representation. -/
theorem finiteBasePolarizedUniversalRepresentation_residue :
    (letI := finiteBasePolarizedCoefficientRing_isLocal a F ha p hp hpa σ ν hν
     ∀ g : finiteBaseArithmeticGaloisGroup a F,
       polarizedCoefficientMap
         (localCoefficientReduction
           (finiteBasePolarizedCoefficientResidueEquiv a F ha p hp hpa σ ν hν)).toRingHom
         (finiteBasePolarizedUniversalRepresentation a F ha p hp hpa σ ν hν g) = σ g) := by
  unfold finiteBasePolarizedUniversalRepresentation finiteBasePolarizedCoefficientResidueEquiv
  exact fixedResidualPolarizedUniversalRepresentation_residue p (finiteBaseArithmeticGaloisGroup a F)
    σ.toMonoidHom (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν

/-- The arithmetic universal representation has exactly the source component and base similitude. -/
theorem finiteBasePolarizedUniversalRepresentation_characters (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedComponent (finiteBasePolarizedUniversalRepresentation a F ha p hp hpa σ ν hν g) =
        polarizedComponent (σ g) ∧
      polarizedSimilitude (finiteBasePolarizedUniversalRepresentation a F ha p hp hpa σ ν hν g) =
        Units.map (algebraMap O (FiniteBasePolarizedCoefficientRing a F ha p hp hpa σ ν)).toMonoidHom (ν g) := by
  unfold finiteBasePolarizedUniversalRepresentation
  exact fixedResidualPolarizedUniversalRepresentation_characters p (finiteBaseArithmeticGaloisGroup a F)
    σ.toMonoidHom (polarizedBlockRepresentation_continuous.comp σ.continuous)
    (finiteBasePolarizedGenerators a F ha p hp hpa σ)
    (finiteBasePolarizedGenerators_surjective a F ha p hp hpa σ) ν hν g

end
end Dubon2026
