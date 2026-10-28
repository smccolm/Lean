import Dubon2026.SourceGammaOneDiamondComplexComparison
import Dubon2026.SourceGammaOneDiamondPicardPeriods
import Dubon2026.SourceGammaOneArithmeticTatePeriods

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison. The proved original arithmetic/complex Picard
square discharges Tate naturality. The actual arithmetic Picard diamond
therefore acts on the p-adic original period lattice by the native dual
slash diamond. No prime restriction or compatibility premise is supplied.
Galois commutation and the original homogeneous coefficient comparison
remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
variable (M p : ℕ) [NeZero M] [Fact p.Prime] (g : Gamma0 M)
local notation "Qbar" => AlgebraicClosure ℚ
local notation "FQ" => functionFieldOver (Gamma1 M) Qbar

theorem tateComplexEquiv_diamond (x : TateModule p (Pic0 Qbar FQ)) :
    ConstantField.tateComplexEquiv M p
        (TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom x) =
      TateModule.tateMap p (complexDiamondPicard M g).toAddMonoidHom
        (ConstantField.tateComplexEquiv M p x) :=
  ConstantField.tateComplexEquiv_naturality M p
    (arithmeticDiamondPicard M g).toAddMonoidHom (complexDiamondPicard M g).toAddMonoidHom
    (ConstantField.complexPicardMap_diamond M g) x

theorem arithmeticPicardTatePeriodTensorEquiv_diamond (x : TateModule p (Pic0 Qbar FQ)) :
    arithmeticPicardTatePeriodTensorEquiv M p
        (TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom x) =
      (periodLatticeDiamond M g).baseChange ℤ_[p]
        (arithmeticPicardTatePeriodTensorEquiv M p x) := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  change complexPicardTatePeriodTensorEquiv M p hT
      (ConstantField.tateComplexEquiv M p
        (TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom x)) =
    (periodLatticeDiamond M g).baseChange ℤ_[p]
      (complexPicardTatePeriodTensorEquiv M p hT (ConstantField.tateComplexEquiv M p x))
  rw [tateComplexEquiv_diamond]
  exact complexPicardTatePeriodTensorEquiv_diamond M g hT p
    (ConstantField.tateComplexEquiv M p x)

end
end Dubon2026.SourceFunctionField.GammaOne
