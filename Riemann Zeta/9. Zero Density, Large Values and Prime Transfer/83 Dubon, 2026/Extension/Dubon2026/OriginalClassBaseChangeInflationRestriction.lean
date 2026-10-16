import Dubon2026.OriginalFullIdeleBaseChangeH2
import Dubon2026.OriginalIdeleClassH2Inflation
import Dubon2026.OriginalIdeleClassH2Restriction

/-! # Original class base change is tower inflation followed by restriction

The coefficient inclusion and automorphism restriction are the literal
maps in both constructions. Compare them on actual H2 cocycles to link
DUB-17's proved auxiliary base-change vanishing with the existing exact
field-tower inflation/restriction theorem.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K E L M : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsGalois K L]

/-- Actual original class base change agrees with actual field-tower inflation followed by actual base restriction, on the same original H2 class. -/
theorem originalFullClassFieldBaseChangeH2_eq_restriction_inflation
    (x : groupCohomology (originalIdeleClassRep K L) 2) :
    groupCohomology.map (galoisBaseChangeRestriction K E L M)
      (originalFullClassFieldBaseChangeRepHom K E L M) 2 x =
      originalIdeleClassTowerH2Restriction K E M
        (groupCohomology.map (AlgEquiv.restrictNormalHom L)
          (originalIdeleClassTowerInclusion K L M) 2 x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.H2π _ c) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    rfl

/-- The class image of the actual scaled full-idele base change is the restriction of the same scaled inflated original class. -/
theorem originalFullIdeleBaseChange_scaled_class_eq_restriction_inflation
    (n : ℕ) (x : groupCohomology (originalFullIdeleRep K L) 2) :
    (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      (n • originalFullIdeleBaseChangeH2 K E L M x) =
      originalIdeleClassTowerH2Restriction K E M
        (n • groupCohomology.map (AlgEquiv.restrictNormalHom L)
          (originalIdeleClassTowerInclusion K L M) 2
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x)) := by
  have h₁ := map_nsmul
    ((groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)).hom.toAddMonoidHom
    n (originalFullIdeleBaseChangeH2 K E L M x)
  have h₂ := (originalFullIdeleBaseChangeH2_class K E L M x).trans
    (originalFullClassFieldBaseChangeH2_eq_restriction_inflation K E L M _)
  have h₃ := map_nsmul (originalIdeleClassTowerH2Restriction K E M).hom.toAddMonoidHom n
    (groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (originalIdeleClassTowerInclusion K L M) 2
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x))
  exact h₁.trans ((congrArg (fun z : groupCohomology (originalIdeleClassRep E M) 2 => n • z) h₂).trans h₃.symm)

end
end Dubon2026
