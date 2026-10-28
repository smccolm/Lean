import Dubon2026.SourceGammaOneArithmeticDiamondTate
import Dubon2026.SourceGammaOneArithmeticPeriodInclusion

/-! DUB-17/18 -> original all-weight association -> original finite Gamma1
homogeneous-coefficient arithmetic realization -> diamond transpose.
The proved arithmetic Tate tensor comparison identifies the action on
the actual period inclusion. This is the missing arithmetic input to
the existing homogeneous-valued lattice/H1 diamond comparison.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
open scoped TensorProduct
variable (M p : ℕ) [NeZero M] [Fact p.Prime] (g : Gamma0 M)

theorem arithmeticPeriodInclusion_diamond (l : sourceWeightTwoIntegralLattice (Gamma1 M)) :
    TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom
        (arithmeticPeriodInclusion M p l) =
      arithmeticPeriodInclusion M p (periodLatticeDiamond M g l) := by
  apply (arithmeticPicardTatePeriodTensorEquiv M p).injective
  rw [arithmeticPicardTatePeriodTensorEquiv_diamond]
  change (periodLatticeDiamond M g).baseChange ℤ_[p]
      ((arithmeticPicardTatePeriodTensorEquiv M p)
        ((arithmeticPicardTatePeriodTensorEquiv M p).symm (1 ⊗ₜ l))) =
    (arithmeticPicardTatePeriodTensorEquiv M p)
      ((arithmeticPicardTatePeriodTensorEquiv M p).symm
        (1 ⊗ₜ (periodLatticeDiamond M g l)))
  simp only [LinearEquiv.apply_symm_apply, LinearMap.baseChange_tmul]

end
end Dubon2026.SourceFunctionField.GammaOne
