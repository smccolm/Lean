import Dubon2026.SourceJointChartOverlapTorsion
import Dubon2026.SourceModularKummerJointChartSpacesR2

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
This is the literal overlap quotient on the actual modular Kummer extension.
Its finite generation is the remaining explicit input to the constants proof. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ

/-- Use the actual coefficient algebra for the modular residue field. -/
local instance overlapSpaceResidueAlgebra (A : ValuationSubring Qbar) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField A)
      (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)) :=
  (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra

/-- The actual two-chart overlap quotient on a modular extension. -/
abbrev modularJointOverlapQuotient (A : ValuationSubring Qbar) (N q : ℕ)
    {E : Type*} [Field E] [Algebra Qbar E]
    (S : Fin q → RegularProlongation A E (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)))
    (t : E) (ht : ∀ i, t ∈ (S i).integers) (hti : ∀ i, t⁻¹ ∈ (S i).integers) :=
  @RegularProlongation.JointChartConstants.overlapQuotient Qbar E inferInstance A inferInstance
    inferInstance (Fin q) (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) : Type))
    (fun _ => inferInstance)
    (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra) S t ht hti

end
end Dubon2026.SourceFunctionField.GaussReduction
