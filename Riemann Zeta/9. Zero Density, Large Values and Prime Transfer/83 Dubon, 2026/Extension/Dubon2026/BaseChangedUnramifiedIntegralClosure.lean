import Dubon2026.BaseChangedUnramifiedTensorImage

/-! # The genuine unramified base-change image is the original integral closure -/

namespace Dubon2026
noncomputable section

variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω] [Algebra B Ω] [IsScalarTower R B Ω]
  {E L : Type*} [Field E] [Field L]
  [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
  (f : A →ₐ[R] Ω) (i : E →+* Ω) (j : L →+* Ω)
  (hi : i.comp (algebraMap B E) = algebraMap B Ω)
  (hj : j.comp (algebraMap A L) = f.toRingHom)
  (htop : i.fieldRange ⊔ j.fieldRange = ⊤)

include hi hj htop

/-- When the original fraction images generate the actual ambient field,
that same field is the fraction field of the genuine base-changed tensor image. -/
theorem baseChangedTensorImage_isFractionRing_of_compositum_top :
    IsFractionRing (BaseChangedTensorImage (B := B) f) Ω := by
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ (baseChangedTensorFractionEmbedding (B := B) f).toRingHom.fieldRange := by
    rw [baseChangedTensorFractionEmbedding_compositum f i j hi hj, htop]
    trivial
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (BaseChangedTensorImage (B := B) f) w
  refine ⟨a, b, ?_⟩
  change IsFractionRing.lift (g := (BaseChangedTensorImage (B := B) f).val.toRingHom)
    Subtype.val_injective (_ / _) = _
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  rfl

variable [IsDedekindDomain B] [Module.Finite R A] [Algebra.FormallyUnramified R A]

/-- The original base-changed image is the actual integral closure of the
new Dedekind base in the genuine fraction-field compositum. -/
theorem baseChangedTensorImage_isIntegralClosure_of_compositum_top :
    IsIntegralClosure (BaseChangedTensorImage (B := B) f) B Ω := by
  haveI := baseChangedTensorImage_finite (B := B) f
  haveI := baseChangedTensorImage_isDedekindDomain (B := B) f
  haveI := baseChangedTensorImage_isFractionRing_of_compositum_top f i j hi hj htop
  exact IsIntegralClosure.of_isIntegrallyClosed (BaseChangedTensorImage (B := B) f) B Ω

/-- The actual integral closure in the compositum is unramified over the
new base. Only the original algebra A over R is required to be unramified. -/
theorem integralClosure_formallyUnramified_of_baseChange_compositum_top
    (C : Type*) [CommRing C] [Algebra B C] [Algebra C Ω]
    [IsScalarTower B C Ω] [IsIntegralClosure C B Ω] :
    Algebra.FormallyUnramified B C := by
  haveI := baseChangedTensorImage_isIntegralClosure_of_compositum_top f i j hi hj htop
  haveI := baseChangedTensorImage_formallyUnramified (B := B) f
  exact Algebra.FormallyUnramified.of_equiv
    (IsIntegralClosure.equiv B (BaseChangedTensorImage (B := B) f) Ω C)

end
end Dubon2026
