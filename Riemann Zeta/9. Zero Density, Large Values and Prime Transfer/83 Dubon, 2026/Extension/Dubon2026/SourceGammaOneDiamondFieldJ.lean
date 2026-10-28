import Dubon2026.SourceGammaOneDiamondFieldHom
import Dubon2026.SourceGammaOneCuspJExactOrder

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond descent. The actual complex diamond fixes the original j coordinate.
Reuse its proved analytic realization and level-one invariance, through the
same injective cusp germ. This is the coordinate needed for algebraic descent.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup UpperHalfPlane Filter
open scoped MatrixGroups Topology
variable (M : ℕ) [NeZero M]

theorem diamondFieldHom_j (g : Gamma0 M) :
    diamondFieldHom M g (jCoordinateOver (Gamma1 M) ℂ) = jCoordinateOver (Gamma1 M) ℂ := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  have he (δ : SL(2, ℤ)) :
      cuspRealize (Gamma1 M) M δ (jCoordinateOver (Gamma1 M) ℂ : LaurentSeries ℂ) =
        cuspFunction M JMultiplicity.jf := by
    unfold cuspRealize
    congr 1
    funext τ
    rw [realize_jCoordinateOver hT, JMultiplicity.jf_smul]
  apply (fieldCuspGerm M 1).injective
  rw [diamondFieldHom_cuspGerm]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun q => by rw [he, he]

end
end Dubon2026.SourceFunctionField.GammaOne
