import Dubon2026.FiniteAdelicLevelResidue

/-! # The original integral Gamma0 matrices inside the genuine finite adelic level and residue groups -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original integral Gamma0 group embeds into the genuine finite adelic general-linear level group. -/
def integralGamma0FiniteGL2Hom (N : ℕ) [NeZero N] : Gamma0 N →* finiteAdeleGL2Gamma0 N where
  toFun γ := ⟨toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ.val),
    finiteAdeleGamma0_toGL_mem N _ ((integralSL2_mem_finiteAdeleGamma0 N γ.val).mpr γ.property)⟩
  map_one' := by
    apply Subtype.ext
    change toGL (Matrix.SpecialLinearGroup.map _ 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    change toGL (Matrix.SpecialLinearGroup.map _ (a.val * b.val)) = _
    rw [map_mul, map_mul]
    rfl

/-- The residue of an actual integral Gamma0 element is its original entrywise integer residue matrix. -/
theorem integralGamma0FiniteGL2Hom_residue (N m : ℕ) [NeZero N] [NeZero m] (γ : Gamma0 N) :
    finiteAdelicLevelResidueHom N m (integralGamma0FiniteGL2Hom N γ) =
      GeneralLinearGroup.map (Int.castRingHom (ZMod m)) (toGL γ.val) := by
  apply Units.ext
  funext i j
  change finiteAdeleResidue m (γ.val i j : finiteAdeleIntegerSubring) = (γ.val i j : ZMod m)
  exact finiteAdeleResidue_intCast m (γ.val i j)

end
end Dubon2026
