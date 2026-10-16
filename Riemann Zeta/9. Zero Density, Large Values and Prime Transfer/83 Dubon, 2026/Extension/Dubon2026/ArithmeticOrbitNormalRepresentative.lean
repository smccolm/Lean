import Dubon2026.ArithmeticOrbitNormalField

/-! # Original finite-stage restriction of a specified coset representative

This keeps the finite global automorphism chosen by prime transitivity
identical to the actual quotient representative used by DUB-17's Mackey
orbit construction.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [Normal ℚ F]

/-- Restricting the chosen coset representative gives exactly the specified representative's original finite-stage action. -/
theorem rationalArithmeticOrbitRepresentative_restrictNormal_mk
    (τ : rationalArithmeticGaloisGroup a) :
    (rationalArithmeticOrbitRepresentative a F (QuotientGroup.mk τ)).restrictNormal F =
      (show Gal(rationalUnramifiedExtension a / ℚ) from τ).restrictNormal F := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact ((rationalArithmeticOrbitRepresentative a F (QuotientGroup.mk τ)).restrictNormal_commutes F x).trans
    ((rationalArithmeticOrbitRepresentative_mk a F τ x).trans
      ((show Gal(rationalUnramifiedExtension a / ℚ) from τ).restrictNormal_commutes F x).symm)

end
end Dubon2026
