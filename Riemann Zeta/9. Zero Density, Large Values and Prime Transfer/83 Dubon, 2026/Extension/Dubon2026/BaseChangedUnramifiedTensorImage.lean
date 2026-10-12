import Dubon2026.AmbientTensorFractionField

/-! # Genuine unramified tensor images after arbitrary integral base change -/

namespace Dubon2026
noncomputable section

open scoped TensorProduct

variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω] [Algebra B Ω] [IsScalarTower R B Ω]

/-- The actual B-linear multiplication map from the genuine base-changed
tensor algebra into the original ambient field. -/
def baseChangedTensorMultiplication (f : A →ₐ[R] Ω) : B ⊗[R] A →ₐ[B] Ω :=
  Algebra.TensorProduct.lift (Algebra.ofId B Ω) f (fun _ _ => Commute.all _ _)

/-- The genuine image retains its original B-algebra structure. -/
abbrev BaseChangedTensorImage (f : A →ₐ[R] Ω) :=
  (baseChangedTensorMultiplication (B := B) f).range

/-- A finite original algebra has a finite actual tensor image over the
new base, without requiring the new base to be finite over the old one. -/
theorem baseChangedTensorImage_finite [Module.Finite R A] (f : A →ₐ[R] Ω) :
    Module.Finite B (BaseChangedTensorImage (B := B) f) :=
  Module.Finite.of_surjective (baseChangedTensorMultiplication (B := B) f).rangeRestrict.toLinearMap
    (baseChangedTensorMultiplication (B := B) f).rangeRestrict_surjective

/-- Original formal unramifiedness survives arbitrary actual base change
and passage to the original tensor image in the ambient field. -/
theorem baseChangedTensorImage_formallyUnramified
    [Algebra.FormallyUnramified R A] (f : A →ₐ[R] Ω) :
    Algebra.FormallyUnramified B (BaseChangedTensorImage (B := B) f) :=
  Algebra.FormallyUnramified.of_surjective (baseChangedTensorMultiplication (B := B) f).rangeRestrict
    (baseChangedTensorMultiplication (B := B) f).rangeRestrict_surjective

/-- Over a genuine Dedekind new base, the actual finite unramified tensor
image is a Dedekind domain. No unramifiedness of B over R is assumed. -/
theorem baseChangedTensorImage_isDedekindDomain [IsDedekindDomain B]
    [Module.Finite R A] [Algebra.FormallyUnramified R A] (f : A →ₐ[R] Ω) :
    IsDedekindDomain (BaseChangedTensorImage (B := B) f) := by
  haveI := baseChangedTensorImage_finite (B := B) f
  haveI := baseChangedTensorImage_formallyUnramified (B := B) f
  exact isDedekindDomain.of_formallyUnramified B (BaseChangedTensorImage (B := B) f)

/-- The genuine tensor-image fraction field embeds in the same original
ambient field through the actual inclusion. -/
def baseChangedTensorFractionEmbedding (f : A →ₐ[R] Ω) :
    FractionRing (BaseChangedTensorImage (B := B) f) →ₐ[B] Ω :=
  IsFractionRing.liftAlgHom (g := (BaseChangedTensorImage (B := B) f).val)
    Subtype.val_injective

/-- Its actual range is exactly the field compositum of the original
fraction fields of the new base and the original unramified algebra. -/
theorem baseChangedTensorFractionEmbedding_compositum
    {E L : Type*} [Field E] [Field L]
    [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
    (f : A →ₐ[R] Ω) (i : E →+* Ω) (j : L →+* Ω)
    (hi : i.comp (algebraMap B E) = algebraMap B Ω)
    (hj : j.comp (algebraMap A L) = f.toRingHom) :
    (baseChangedTensorFractionEmbedding (B := B) f).toRingHom.fieldRange =
      i.fieldRange ⊔ j.fieldRange := by
  change (IsFractionRing.lift (K := FractionRing (BaseChangedTensorImage (B := B) f))
    (g := (BaseChangedTensorImage (B := B) f).val.toRingHom)
    Subtype.val_injective).fieldRange = _
  rw [IsFractionRing.lift_fieldRange]
  have hr : Set.range (fun x : BaseChangedTensorImage (B := B) f => (x : Ω)) =
      (BaseChangedTensorImage (B := B) f : Set Ω) := Subtype.range_val
  change Subfield.closure (Set.range (fun x : BaseChangedTensorImage (B := B) f => (x : Ω))) = _
  rw [hr]
  change Subfield.closure (AmbientTensorImage (IsScalarTower.toAlgHom R B Ω) f : Set Ω) = _
  rw [ambientTensorImage_fieldClosure, Subfield.closure_union]
  exact congrArg₂ (· ⊔ ·) (IsFractionRing.ringHom_fieldRange_eq_of_comp_eq hi).symm
    (IsFractionRing.ringHom_fieldRange_eq_of_comp_eq hj).symm

end
end Dubon2026
