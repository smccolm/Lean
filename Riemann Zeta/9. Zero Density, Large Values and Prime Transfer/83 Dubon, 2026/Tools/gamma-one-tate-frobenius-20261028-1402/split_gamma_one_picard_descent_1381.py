from pathlib import Path
p=Path(__file__).parent
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('SourceGammaOneHeckePicardDescent1381a.lean','''import SourceGammaOneResiduePicard1375a
import SourceGammaOneNormDiamondOrientation1377b
import Dubon2026.SourceGammaOneHeckePicard
import Dubon2026.SourceCurveReductionPicardR2

/-! DUB-17/18 -> original Gamma1 Frobenius -> descent of the proved
integer-divisor correspondence. Apply the actual Picard quotient to one
literal divisor equality. The subsequent original norm consumer supplies
that equality on every finite torsion class; no compatibility is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup ConstantField
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
  rw [hdiamond]
  change Pic0.mk (R.degZeroMap ⟨heckeDivisor Qbar M p D.val,
    heckeDivisor_mem_degZero Qbar M p D.property⟩) =
    Pic0.mk (decompositionResidueDegZero A Γ hT d (R.degZeroMap E)) +
      p • Pic0.mk (decompositionResidueDegZero A Γ hT d⁻¹ (R.degZeroMap D))
  rw [← map_nsmul, ← map_add]
  apply congrArg Pic0.mk
  apply Subtype.ext
  change R.divMap (heckeDivisor Qbar M p D.val) =
    decompositionResidueDivisorEquiv A Γ d
      (R.divMap (fieldDivisorEquiv (arithmeticDiamondAut M g) D.val)) +
    p • decompositionResidueDivisorEquiv A Γ d⁻¹ (R.divMap D.val)
  rw [← decompositionResidueDivisorEquiv_symm]
  exact hdiv

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
f=p/'SourceGammaOneHeckeTorsionPicard1378c.lean';s=f.read_text(encoding='utf-8')
s='import SourceGammaOneHeckePicardDescent1381a\n'+s
a=s.index('  have hT : ModularGroup.T ∈ Γ')
b=s.index('\nend\n',a)
s=s[:a]+'''  exact hecke_picard_reduction_mk_of_divisor_eq A M p R g d D (hdiv R hR D m hm hx)
'''+s[b:]
out('SourceGammaOneHeckeTorsionPicard1378d.lean',s)
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
for old,new,a,b in [('SourceGammaOnePicardFrobeniusRelation1379d','SourceGammaOnePicardFrobeniusRelation1379e','SourceGammaOneHeckeTorsionPicard1378c','SourceGammaOneHeckeTorsionPicard1378d'),('SourceGammaOneTateFrobeniusRelation1380a','SourceGammaOneTateFrobeniusRelation1380b','SourceGammaOnePicardFrobeniusRelation1379d','SourceGammaOnePicardFrobeniusRelation1379e')]:
 f=p/(old+'.lean');out(new+'.lean',f.read_text(encoding='utf-8').replace(a,b))
 assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneHeckePicardDescent1381a','SourceGammaOneHeckeTorsionPicard1378d','SourceGammaOnePicardFrobeniusRelation1379e','SourceGammaOneTateFrobeniusRelation1380b')")
out('build_gamma_one_picard_descent_1381.ps1',s)
