import Dubon2026.SourceJointChartWeightedSpans
import Dubon2026.SourceModularKummerRegularReductionsR2

/-! DUB-17/18 -> Kummer genus inequality -> simultaneous residue chart
dimensions. These are the literal chart submodules on the modular Kummer
extension; explicit coefficient algebras avoid unrelated tower inference. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ

/-- Use the actual coefficient algebra when forming the chart submodules. -/
local instance chartSpaceResidueModularAlgebra (A : ValuationSubring Qbar) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField A)
      (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)) :=
  (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra

/-- The residue span of an actual coordinate chart on a modular extension. -/
def modularJointChart (A : ValuationSubring Qbar) (N q : ℕ)
    {E : Type*} [Field E] [Algebra Qbar E]
    (S : Fin q → RegularProlongation A E (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)))
    (t : E) : Submodule (IsLocalRing.ResidueField A)
      (Fin q → modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)) :=
  @RegularProlongation.JointChartAssembly.ST Qbar inferInstance A E inferInstance
    inferInstance (Fin q) (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) : Type))
    (fun _ => inferInstance) (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra) S t

/-- The weighted inverse-chart residue span on the actual modular extension. -/
def modularJointWeightedChart (A : ValuationSubring Qbar) (N q : ℕ)
    {E : Type*} [Field E] [Algebra Qbar E]
    (S : Fin q → RegularProlongation A E (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)))
    (t : E) (M : ℕ) : Submodule (IsLocalRing.ResidueField A)
      (Fin q → modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)) :=
  @RegularProlongation.JointChartAssembly.weightedST Qbar E inferInstance A inferInstance
    inferInstance (Fin q) (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A) : Type))
    (fun _ => inferInstance) (fun _ => (modularFunctionFieldCoeff N (IsLocalRing.ResidueField A)).toSubalgebra.algebra) S t M

end
end Dubon2026.SourceFunctionField.GaussReduction
