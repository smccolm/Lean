import Dubon2026.OriginalRationalExceptionalClassTransition
import Dubon2026.OriginalIdeleBaseChangeTower

/-! # Exact exceptional-class transport through the scalar-stage tower

The already proved original idele-class base-change composition descends
to the same outside-unit quotients. This retains the constructed relation
coefficient when DUB-17's scalar stage is realized in the arithmetic union.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.Quotient.module
variable (E F L : Type) [Field E] [NumberField E] [Field F] [NumberField F]
  [Field L] [NumberField L]
  [Algebra ℚ E] [Algebra ℚ F] [Algebra ℚ L]
  [Algebra E F] [Algebra F L] [Algebra E L]
  [IsScalarTower ℚ E F] [IsScalarTower ℚ F L] [IsScalarTower ℚ E L]
  [IsScalarTower E F L] [IsGalois ℚ E] [IsGalois ℚ F]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Successive original exceptional-class transitions preserve exactly
the same class as the direct tower inclusion. -/
theorem originalRationalExceptionalClassTransition_tower
    (x : originalIdeleClassesModOutsideRep ℚ E
      (originalExceptionalIntegerSupport E (algebraMap (𝓞 ℚ) (𝓞 E) a)
        (originalIntegerMap_ne_zero (L := E) a ha))
      (originalExceptionalIntegerSupport_galoisStable E ℚ a ha)) :
    (originalRationalExceptionalClassTransition F L a ha).hom
      ((originalRationalExceptionalClassTransition E F a ha).hom x) =
      (originalRationalExceptionalClassTransition E L a ha).hom x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    apply congrArg Submodule.Quotient.mk
    exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_tower E F L x.toMul)

end
end Dubon2026
