import Dubon2026.SourceOriginalCoefficientDivisors
import Dubon2026.SourceCurveReductionPicardR2
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> original Picard inertia -> descent of the proved
original-place invariance. Literal finite-support pushforward commutes
with the original divisor action after reduction. This is a consequence
of the previously derived place identity, proved on every finite divisor. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "F" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra

theorem reduction_originalArithmeticDivisor
    (R : ConstantReduction A F Fb) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hplace : ∀ P : Place Qbar Fo,
      R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P)) =
        R.placeMap (originalCoefficientPlaceEquiv N P)) (D : Divisor Qbar Fo) :
    R.divMap (originalCoefficientDivisorEquiv N (originalArithmeticDivisorEquiv N τ D)) =
      R.divMap (originalCoefficientDivisorEquiv N D) := by
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, map_add, map_add, map_add, ih]
    congr 1
    change Finsupp.mapDomain R.placeMap
        (Finsupp.equivMapDomain (originalCoefficientPlaceEquiv N)
          (Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N τ) (Finsupp.single P n))) =
      Finsupp.mapDomain R.placeMap
        (Finsupp.equivMapDomain (originalCoefficientPlaceEquiv N) (Finsupp.single P n))
    rw [Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single,
      Finsupp.equivMapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    exact congrArg (fun Q => Finsupp.single Q n) (hplace P)

end
end Dubon2026.SourceFunctionField.GaussReduction
