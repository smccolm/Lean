import Dubon2026.SourceOriginalTorsionDivisorAgreement
import Dubon2026.SourceOriginalHeckeIntegralAgreement
import Dubon2026.SourceResidueFrobeniusPicardOperator
import Dubon2026.SourceOriginalCoefficientPicard

/-! DUB-17/18 -> original Tate quadratic relation -> original Hecke
compatibility on finite torsion. Apply the proved torsion-free divisor
cancellation argument to the actual integral-principal Hecke agreement,
then descend the resulting divisor equality to the native Picard quotient.
All compatibility premises of the cancellation argument are discharged. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N p : ℕ) [NeZero N] [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField A) p]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem original_hecke_reduction_torsion_divisor
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0) (R : ConstantReduction A FF Fb)
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (D : Divisor.degZero (K := Qbar) (F := Fo)) (m : ℕ) (hm : m ≠ 0)
    (hD : m • Pic0.mk D = 0) :
    R.divMap (originalCoefficientDivisorEquiv N (originalHeckeDivisor Qbar N p D.val)) =
      residueFrobeniusDivisorOperator N kk p
        (R.divMap (originalCoefficientDivisorEquiv N D.val)) := by
  exact original_divisor_hom_eq_on_torsion A N
    (R.divMap.comp ((originalCoefficientDivisorEquiv N).toAddMonoidHom.comp
      (originalHeckeDivisor Qbar N p)))
    ((residueFrobeniusDivisorOperator N kk p).comp
      (R.divMap.comp (originalCoefficientDivisorEquiv N).toAddMonoidHom))
    (fun y hy hry => original_hecke_reduction_integral_principal A N p hpN hNk R hR y hy hry)
    D m hm hD

theorem original_hecke_reduction_torsion_picard
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0) (R : ConstantReduction A FF Fb)
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (x : Pic0 Qbar Fo) (m : ℕ) (hm : m ≠ 0) (hx : m • x = 0) :
    R.pic0Map (originalCoefficientPicardEquiv N (originalHeckePicard Qbar N p x)) =
      residueFrobeniusPicardOperator N kk p
        (R.pic0Map (originalCoefficientPicardEquiv N x)) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  change Pic0.mk (R.degZeroMap (originalCoefficientDegZeroEquiv N
    ⟨originalHeckeDivisor Qbar N p D.val, originalHeckeDivisor_mem_degZero Qbar N p D.property⟩)) =
      residueFrobeniusPicardOperator N kk p
        (Pic0.mk (R.degZeroMap (originalCoefficientDegZeroEquiv N D)))
  rw [residueFrobeniusPicardOperator_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact original_hecke_reduction_torsion_divisor A N p hpN hNk R hR D m hm hx

end
end Dubon2026.SourceFunctionField.GaussReduction
