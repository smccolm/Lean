import Dubon2026.SourceIntegralDiamondScalarFixedField
import Dubon2026.SourceOriginalResidueCoordinateIndex
import Dubon2026.SourceGammaOneResidueSeparability

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> residue fiber bounds. The original degree-preservation theorem discharges
the coordinate-degree premise of the fixed-field comparison for the actual
valuation residue field. The action uses the canonical prime-field embedding;
there is no assumed action, fixed-field identity or degree-preservation input.
-/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open IntermediateField CongruenceSubgroup GammaOne GammaOne.CoefficientReduction
open scoped MatrixGroups
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra

/-- The actual diamond action on the original valuation-residue integral-ratio field. -/
def originalResidueDiamondAction (hℓN : ¬ ℓ ∣ N) :
    Gamma0 N →* (qExpFunctionFieldC kk (Gamma1 N) ≃ₐ[kk]
      qExpFunctionFieldC kk (Gamma1 N)) := by
  letI : Algebra (ZMod ℓ) kk := (ZMod.castHom (dvd_refl ℓ) kk).toAlgebra
  exact reducedFieldActionOver kk N ℓ hℓN

theorem originalResidueDiamond_fixedField_eq_fullBase (hℓN : ¬ ℓ ∣ N) :
    lift (IntermediateField.fixedField (originalResidueDiamondAction A N ℓ hℓN).range) =
      modularFunctionFieldCoeff N kk := by
  letI : Algebra (ZMod ℓ) kk := (ZMod.castHom (dvd_refl ℓ) kk).toAlgebra
  letI := valuation_residue_isAlgClosed A
  exact scalar_fixedField_eq_fullBase_of_coordinate_degree kk N ℓ hℓN
    (residue_original_coordinate_degree_eq_signed_index A N ℓ hℓN)

end
end Dubon2026.SourceFunctionField.IntegralDiamond
