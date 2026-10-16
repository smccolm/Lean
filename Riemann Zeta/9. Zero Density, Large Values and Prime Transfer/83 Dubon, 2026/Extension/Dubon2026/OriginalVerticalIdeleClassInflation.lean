import Dubon2026.OriginalFullIdeleBaseChangeH2
import Dubon2026.OriginalIdeleClassH2Inflation

/-! # The actual class projection of vertical idele base change

With the same lower field, base change uses the original tower restriction
and original coefficient inclusion. Their cocycle maps agree. This connects
preservation of the canonical idele total to injective class inflation in
DUB-17's finite-stage normalization argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K L M : Type) [Field K] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L]

/-- Projecting actual vertical idele base change gives the original class-tower inflation of the source projection. -/
theorem originalFullIdeleBaseChangeH2_vertical_class
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    (groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M)
      (originalFullIdeleBaseChangeH2 K K L M x) =
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (originalIdeleClassTowerInclusion K L M) 2
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_mk L M _).symm

end
end Dubon2026
