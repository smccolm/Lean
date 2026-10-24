import Dubon2026.SourceModularKummerJointChartSpacesR2

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap. The
literal vector of residues on the actual modular reduction family, with
its coefficient algebra fixed explicitly to avoid unrelated tower search. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve

/-- Fix the actual residue coefficient algebra for the family declaration. -/
local instance jointVectorResidueAlgebra (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField A)
      (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)) :=
  (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra

/-- The simultaneous residue vector on the actual modular extension. -/
abbrev modularJointResidueVector (A : ValuationSubring (AlgebraicClosure ℚ)) (N q : ℕ)
    {E : Type*} [Field E] [Algebra (AlgebraicClosure ℚ) E]
    (S : Fin q → RegularProlongation A E
      (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)))
    (x : E) (hx : ∀ i, x ∈ (S i).integers) :
    Fin q → modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) :=
  @RegularProlongation.JointChartAssembly.rv (AlgebraicClosure ℚ) inferInstance A E
    inferInstance inferInstance (Fin q)
    (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) : Type))
    (fun _ => inferInstance)
    (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra)
    S x hx

end
end Dubon2026.SourceFunctionField.GaussReduction
