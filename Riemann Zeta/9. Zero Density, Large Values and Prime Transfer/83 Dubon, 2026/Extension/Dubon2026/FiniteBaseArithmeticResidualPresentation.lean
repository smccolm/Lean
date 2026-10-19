import Dubon2026.ArithmeticOpenResidualPresentation
import Dubon2026.FiniteBaseGaloisTopology

/-! Actual finite-base arithmetic Galois groups, their original Krull
topology and finite residual presentations. These provide the genuine
base-field group input to DUB-17's polarized CM deformation construction;
the modular residual representation remains a separate arithmetic obligation. -/

namespace Dubon2026
open Matrix
open scoped NumberField
noncomputable section

/-- Retain the actual rational algebra of the original arithmetic extension. -/
local instance finiteBaseArithmeticUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F]

/-- The actual original arithmetic subgroup fixing the specified finite base field. -/
abbrev finiteBaseArithmeticGaloisGroup : ProfiniteGrp :=
  arithmeticOpenSubgroupProfinite a ⟨F.fixingSubgroup, F.fixingSubgroup_isOpen⟩

/-- The original fixing group is the actual automorphism group over the same finite field. -/
def finiteBaseArithmeticGaloisEquiv :
    finiteBaseArithmeticGaloisGroup a F ≃* Gal(rationalUnramifiedExtension a / F) :=
  IntermediateField.fixingSubgroupEquiv F

/-- The finite-base identification preserves the genuine original Krull topology. -/
theorem finiteBaseArithmeticGaloisEquiv_continuous :
    Continuous (finiteBaseArithmeticGaloisEquiv a F) :=
  finiteBase_fixingSubgroupEquiv_continuous F

/-- The inverse finite-base identification also preserves the original Krull topology. -/
theorem finiteBaseArithmeticGaloisEquiv_symm_continuous :
    Continuous (finiteBaseArithmeticGaloisEquiv a F).symm := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  exact finiteBase_fixingSubgroupEquiv_symm_continuous F

/-- Actual continuous residual matrices over a finite arithmetic base have a
surjective finite-generator presentation; no generating set or character finiteness is assumed. -/
theorem finiteBaseArithmeticResidual_has_profinite_presentation
    {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace R] [DiscreteTopology R]
    (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ρ : finiteBaseArithmeticGaloisGroup a F →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) :
    (let hK := ρ.ker.isClosed_of_isOpen (continuousMatrixRepresentation_isOpen_ker ρ hρ)
     ∃ S : Finset (fixedResidualProfiniteQuotient p (finiteBaseArithmeticGaloisGroup a F) ρ.ker hK),
       Function.Surjective (profiniteGeneratorPresentation
         (fixedResidualProfiniteQuotient p (finiteBaseArithmeticGaloisGroup a F) ρ.ker hK) S)) :=
  arithmeticOpenResidual_has_profinite_presentation a ha p hp hpa
    ⟨F.fixingSubgroup, F.fixingSubgroup_isOpen⟩ ρ hρ

end
end Dubon2026
