import Dubon2026.FiniteBaseArithmeticResidualPresentation
import Dubon2026.PolarizedBlockContinuity
import Dubon2026.FixedResidualFramedCoefficientRing

/-! Actual finite generators for the original continuous polarized residual
representation over a finite arithmetic base. The arithmetic character
finiteness theorem supplies these generators; DUB-17's coefficient quotient
does not need a separate finite-generation premise for this base group. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Retain the actual rational algebra on the finite-base arithmetic extension. -/
local instance finiteBasePolarizedUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable {ι O : Type} [Fintype ι] [DecidableEq ι] [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)] [DiscreteTopology (IsLocalRing.ResidueField O)]
  (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
  (σ : finiteBaseArithmeticGaloisGroup a F →ₜ*
    PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))

/-- Finitely many original residual generators chosen from the proved arithmetic presentation. -/
def finiteBasePolarizedGenerators :
    Finset (originalResidualProfiniteGroup p (finiteBaseArithmeticGaloisGroup a F)
      (polarizedBlockRepresentation.comp σ.toMonoidHom)
      (polarizedBlockRepresentation_continuous.comp σ.continuous)) :=
  Classical.choose (finiteBaseArithmeticResidual_has_profinite_presentation a F ha p hp hpa
    (polarizedBlockRepresentation.comp σ.toMonoidHom)
    (polarizedBlockRepresentation_continuous.comp σ.continuous))

/-- The constructed arithmetic generators present the entire original residual quotient. -/
theorem finiteBasePolarizedGenerators_surjective :
    Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p (finiteBaseArithmeticGaloisGroup a F)
        (polarizedBlockRepresentation.comp σ.toMonoidHom)
        (polarizedBlockRepresentation_continuous.comp σ.continuous))
      (finiteBasePolarizedGenerators a F ha p hp hpa σ)) :=
  Classical.choose_spec (finiteBaseArithmeticResidual_has_profinite_presentation a F ha p hp hpa
    (polarizedBlockRepresentation.comp σ.toMonoidHom)
    (polarizedBlockRepresentation_continuous.comp σ.continuous))

end
end Dubon2026
