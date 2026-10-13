import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology
import Dubon2026.GaloisTowerQuotientUnitCoefficients

/-! # Original idele-class coefficients in finite Galois towers

Actual field restriction identifies its kernel action with the original
upper extension action, whose H1 now vanishes. Actual middle-field class
inclusion identifies the quotient invariant coefficients. These supply
faithful H2 inflation between finite stages, needed to construct a coherent
global class invariant and compare its local restrictions on DUB-17's
arithmetic duality chain. No absolute idele-class model is introduced.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L : Type) [Field K] [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]

/-- The original upper idele-class action is the restriction-kernel action. -/
def originalIdeleClassTowerKernelCoefficientIso :
    Rep.res (galoisTowerKernelEquiv K E L).toMonoidHom (originalIdeleClassRep E L) ≅
      Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype
        (originalIdeleClassRep K L) :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive (OriginalNumberFieldIdeleClassGroup L))
    isIntertwining' g := by ext x; rfl }

/-- The actual restriction kernel has vanishing original class H1. -/
theorem originalIdeleClassTowerKernel_first_zero :
    Limits.IsZero (groupCohomology
      (Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype
        (originalIdeleClassRep K L)) 1) := by
  haveI : FiniteDimensional E L := FiniteDimensional.right K E L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  let e := originalCohomologyReindex (originalIdeleClassRep E L)
      (galoisTowerKernelEquiv K E L) 1 ≪≫
    (groupCohomology.functor ℤ
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker 1).mapIso
        (originalIdeleClassTowerKernelCoefficientIso K E L)
  exact (originalIdeleClass_finiteGalois_first_zero E L).of_iso e.symm

/-- Actual middle-field class inclusion lands in the original kernel invariants. -/
def originalIdeleClassTowerQuotientInclusion :
    Rep.res (galoisTowerQuotientEquiv K E L).toMonoidHom (originalIdeleClassRep K E) ⟶
      (originalIdeleClassRep K L).quotientToInvariants
        (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker := by
  refine Rep.ofHom ⟨((originalIdeleClassBaseChangeMap E L).toAdditive.toIntLinearMap).codRestrict
    _ (fun u s => ?_), fun q => ?_⟩
  · exact congrArg Additive.ofMul
      (originalIdeleClassBaseChangeMap_fixed E L (galoisTowerKernelEquiv K E L s) u.toMul)
  · apply LinearMap.ext
    intro u
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      exact congrArg Additive.ofMul
        (originalIdeleClassBaseChangeMap_restrictNormal K E L g u.toMul).symm

/-- Original class descent makes the actual quotient invariant inclusion bijective. -/
theorem originalIdeleClassTowerQuotientInclusion_bijective :
    Function.Bijective (originalIdeleClassTowerQuotientInclusion K E L).hom := by
  haveI : FiniteDimensional E L := FiniteDimensional.right K E L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  constructor
  · intro u v huv
    apply Additive.toMul.injective
    apply originalIdeleClassBaseChangeMap_injective E L
    exact congrArg (fun z => Additive.toMul z.val) huv
  · intro x
    obtain ⟨u, hu⟩ := originalIdeleClassBaseChangeMap_surjective_fixed E L x.val.toMul
      (fun σ => congrArg Additive.toMul
        (x.property ((galoisTowerKernelEquiv K E L).symm σ)))
    exact ⟨Additive.ofMul u, Subtype.ext (congrArg Additive.ofMul hu)⟩

end
end Dubon2026
