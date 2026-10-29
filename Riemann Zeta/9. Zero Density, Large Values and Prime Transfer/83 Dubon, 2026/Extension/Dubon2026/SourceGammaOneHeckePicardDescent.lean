import Dubon2026.SourceGammaOneGenusSpecialization
import Dubon2026.SourceGammaOneResiduePicard
import Dubon2026.SourceGammaOneNormDiamondOrientation
import Dubon2026.SourceGammaOneHeckePicard
import Dubon2026.SourceCurveReductionPicardR2

/-! DUB-17/18 -> original Gamma1 Frobenius -> descent of the proved
integer-divisor correspondence. Apply the actual Picard quotient to one
literal divisor equality. The subsequent original norm consumer supplies
that equality on every finite torsion class; no compatibility is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup ConstantField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M p : ℕ) [NeZero M] [NeZero p]
local notation "Γ" => Gamma1 M
local notation "FF" => laurentBaseChange Qbar (x1FunctionField M)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem hecke_picard_reduction_mk_of_divisor_eq
    (R : ConstantReduction A FF Fb) (g : Gamma0 M) (d : A.decompositionSubgroup ℚ)
    (D : Divisor.degZero (K := Qbar) (F := FF))
    (hdiv : R.divMap (heckeDivisor Qbar M p D.val) =
      decompositionResidueDivisorEquiv A Γ d
        (R.divMap (fieldDivisorEquiv (arithmeticDiamondAut M g) D.val)) +
      p • (decompositionResidueDivisorEquiv A Γ d).symm (R.divMap D.val)) :
    R.pic0Map (heckePicard Qbar M p (Pic0.mk D)) =
      decompositionResiduePicard A Γ (by simp [Gamma1_mem, ModularGroup.T]) d
        (R.pic0Map (arithmeticDiamondPicard M g⁻¹ (Pic0.mk D))) +
      p • decompositionResiduePicard A Γ (by simp [Gamma1_mem, ModularGroup.T]) d⁻¹
        (R.pic0Map (Pic0.mk D)) := by
  have hT : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, ModularGroup.T]
  let E := fieldDegZeroEquiv (arithmeticDiamondAut M g)
    (functionFieldOver_residue_bijective Γ hT)
    (functionFieldOver_residue_bijective Γ hT) D
  have hdiamond : arithmeticDiamondPicard M g⁻¹ (Pic0.mk D) = Pic0.mk E :=
    arithmeticDiamondPicard_inverse_lift_mk M g D
  have hzero : R.degZeroMap ⟨heckeDivisor Qbar M p D.val,
      heckeDivisor_mem_degZero Qbar M p D.property⟩ =
      decompositionResidueDegZero A Γ hT d (R.degZeroMap E) +
        p • decompositionResidueDegZero A Γ hT d⁻¹ (R.degZeroMap D) := by
    apply Subtype.ext
    change R.divMap (heckeDivisor Qbar M p D.val) =
      decompositionResidueDivisorEquiv A Γ d
        (R.divMap (fieldDivisorEquiv (arithmeticDiamondAut M g) D.val)) +
      p • decompositionResidueDivisorEquiv A Γ d⁻¹ (R.divMap D.val)
    rw [← decompositionResidueDivisorEquiv_symm]
    exact hdiv
  let q : Divisor.degZero (K := kk) (F := Fb) →+ Pic0 kk Fb := Pic0.mk
  let Y := decompositionResidueDegZero A Γ hT d (R.degZeroMap E)
  let Z := decompositionResidueDegZero A Γ hT d⁻¹ (R.degZeroMap D)
  have hmap : q (Y + p • Z) = q Y + p • q Z :=
    (q.map_add Y (p • Z)).trans (congrArg (fun z => q Y + z) (q.map_nsmul p Z))
  have hclass := (congrArg q hzero).trans hmap
  change R.pic0Map (heckePicard Qbar M p (Pic0.mk D)) =
    decompositionResiduePicard A Γ hT d (R.pic0Map (Pic0.mk E)) +
      p • decompositionResiduePicard A Γ hT d⁻¹ (R.pic0Map (Pic0.mk D)) at hclass
  exact hclass.trans (congrArg (fun z =>
    decompositionResiduePicard A Γ hT d (R.pic0Map z) +
      p • decompositionResiduePicard A Γ hT d⁻¹ (R.pic0Map (Pic0.mk D))) hdiamond.symm)

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
