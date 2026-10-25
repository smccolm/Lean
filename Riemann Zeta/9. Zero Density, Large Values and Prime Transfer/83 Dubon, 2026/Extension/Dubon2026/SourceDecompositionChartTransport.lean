import Dubon2026.SourceResidueCoefficientPlaces
import Dubon2026.SourceOriginalInertiaChartTransport
import Dubon2026.SourceArithmeticFrobeniusResidue

/-! DUB-17/18 -> original arithmetic Frobenius/Picard comparison ->
the exact two-chart place reduction. The inverse decomposition action on
integral functions and constants agrees with the inverse native residue
action. Existing original chart stability and Gauss equivariance therefore
transport the actual chart reduction condition on both sides. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra

theorem chartReducesTo_decomposition (hNk : (N : kk) ≠ 0)
    (d : A.decompositionSubgroup ℚ) (P : Place Qbar FF) (Q : Place kk Fb)
    (y : FF) (hy : coefficientArithmeticRingAut N d.val.symm y = y)
    (hP : ChartReducesTo A
      (modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk) y P Q) :
    ChartReducesTo A
      (modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk) y
      (coefficientArithmeticPlace N d.val P)
      (residueCoefficientPlace N kk (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d) Q) := by
  intro f hf a ha
  let f' := decompositionGaussHom A N d⁻¹ f
  have hf' : IsIntegral (Algebra.adjoin Qbar {y}) (f' : FF) :=
    coefficientArithmeticRingAut_isIntegral N d.val.symm y hy hf
  have ha' : (f' : FF) - algebraMap Qbar FF (d⁻¹ • a) ∈ P.toValuationSubring.nonunits := by
    have h := (nonunit_coefficientArithmeticPlace_iff N d.val P _).mp ha
    rw [map_sub, coefficientArithmeticRingAut_constants] at h
    exact h
  have h := hP f' hf' (d⁻¹ • a) ha'
  have hr := decompositionGaussHom_modularResidue A N hNk d⁻¹ f
  rw [map_inv] at hr
  change modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f' = _ at hr
  change modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f -
    algebraMap kk Fb (IsLocalRing.residue A a) ∈
      (residueCoefficientPlace N kk
        (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d) Q).toValuationSubring.nonunits
  rw [nonunit_residueCoefficientPlace_iff, map_sub]
  erw [residueCoefficientRingAut_constants N kk
      (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d).symm (IsLocalRing.residue A a), ← hr]
  have hc : (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d).symm
      (IsLocalRing.residue A a) = IsLocalRing.residue A (d⁻¹ • a) := by
    rw [IsLocalRing.ResidueField.residue_smul]
    rfl
  rw [hc]
  exact h

end
end Dubon2026.SourceFunctionField.GaussReduction
