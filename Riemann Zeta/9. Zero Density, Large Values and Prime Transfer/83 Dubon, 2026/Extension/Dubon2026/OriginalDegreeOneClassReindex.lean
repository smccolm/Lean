import Dubon2026.OriginalIdeleClassSubgroupCohomology

/-! # Original class cohomology under a degree-one base realization

The same upper field and original idele class group are retained. An actual
surjective base inclusion changes only the displayed fixed field. This is
the comparison needed to return DUB-17's unrestricted arithmetic construction
to the original rational base.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (K F L : Type) [Field K] [Field F] [Field L] [NumberField L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  (hs : Function.Surjective (algebraMap K F))

/-- Restriction of scalars is the actual Galois-group equivalence for a
surjective base inclusion. -/
def originalSurjectiveBaseGaloisEquiv : Gal(L/F) ≃* Gal(L/K) where
  toFun σ := σ.restrictScalars K
  invFun σ := σ.extendScalarsOfSurjective hs
  left_inv σ := by ext x; rfl
  right_inv σ := rfl
  map_mul' σ τ := rfl

/-- The original class action is unchanged under this base equivalence. -/
def originalSurjectiveBaseClassCoefficientIso :
    Rep.res (originalSurjectiveBaseGaloisEquiv K F L hs).toMonoidHom
      (originalIdeleClassRep K L) ≅ originalIdeleClassRep F L :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive (OriginalNumberFieldIdeleClassGroup L))
    isIntertwining' g := by ext x; rfl }

/-- The genuine cohomology reindexing identifies the original class groups
in every degree without changing the coefficient or its action. -/
def originalSurjectiveBaseClassCohomologyIso (n : ℕ) :
    groupCohomology (originalIdeleClassRep K L) n ≅
      groupCohomology (originalIdeleClassRep F L) n :=
  originalCohomologyReindex _ (originalSurjectiveBaseGaloisEquiv K F L hs) n ≪≫
    (groupCohomology.functor ℤ Gal(L/F) n).mapIso
      (originalSurjectiveBaseClassCoefficientIso K F L hs)

end
end Dubon2026
