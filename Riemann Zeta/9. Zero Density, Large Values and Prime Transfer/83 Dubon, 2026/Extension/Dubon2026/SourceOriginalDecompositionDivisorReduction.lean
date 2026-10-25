import Dubon2026.SourceOriginalCoefficientDivisors
import Dubon2026.SourceResidueCoefficientDivisors
import Dubon2026.SourceCurveReductionPicardR2
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> original Frobenius/Picard comparison -> finite divisors.
The actual original and residue place actions commute with reduction, so
their literal finite-support pushforwards commute as well. The following
Picard consumer discharges this place equation using the two-chart proof. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra

theorem reduction_originalArithmeticDivisor_equivariant
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar) (e : kk ≃+* kk)
    (hplace : ∀ P : Place Qbar Fo,
      R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P)) =
        residueCoefficientPlace N kk e (R.placeMap (originalCoefficientPlaceEquiv N P)))
    (D : Divisor Qbar Fo) :
    R.divMap (originalCoefficientDivisorEquiv N (originalArithmeticDivisorEquiv N τ D)) =
      residueCoefficientDivisorEquiv N kk e (R.divMap (originalCoefficientDivisorEquiv N D)) := by
  induction D using Finsupp.induction with
  | zero =>
    simp only [map_zero]
    exact (map_zero (residueCoefficientDivisorEquiv N kk e)).symm
  | single_add P n D _ _ ih =>
    erw [map_add, map_add, map_add, map_add, map_add, map_add, ih]
    congr 1
    change Finsupp.mapDomain R.placeMap
        (Finsupp.equivMapDomain (originalCoefficientPlaceEquiv N)
          (Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N τ) (Finsupp.single P n))) =
      Finsupp.equivMapDomain (residueCoefficientPlaceEquiv N kk e)
        (Finsupp.mapDomain R.placeMap
          (Finsupp.equivMapDomain (originalCoefficientPlaceEquiv N) (Finsupp.single P n)))
    rw [Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single,
      Finsupp.equivMapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      Finsupp.equivMapDomain_single]
    exact congrArg (fun Q => Finsupp.single Q n) (hplace P)

end
end Dubon2026.SourceFunctionField.GaussReduction
