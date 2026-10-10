import Dubon2026.AmbientTensorFractionField

/-! # The actual tensor image is the integral closure inside the original compositum -/

namespace Dubon2026

noncomputable section

variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω]

/-- The genuine fraction embedding preserves the original base algebra. -/
def ambientTensorFractionAlgebraEmbedding (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) :
    FractionRing (AmbientTensorImage f g) →ₐ[R] Ω :=
  IsFractionRing.liftAlgHom (g := (AmbientTensorImage f g).val) Subtype.val_injective

/-- The actual fraction embedding has the original ambient value on every original tensor-image coefficient. -/
theorem ambientTensorFractionAlgebraEmbedding_original
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (a : AmbientTensorImage f g) :
    ambientTensorFractionAlgebraEmbedding f g
      (algebraMap (AmbientTensorImage f g) (FractionRing (AmbientTensorImage f g)) a) =
        (a : Ω) :=
  IsFractionRing.lift_algebraMap Subtype.val_injective a

/-- For genuine finite unramified input algebras over the original Dedekind base, the actual tensor image consists precisely of the original base-integral elements in the literal compositum of the original fraction-field images. -/
theorem ambientTensorImage_mem_iff_compositum_integral [IsDedekindDomain R]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified R B]
    {L M : Type*} [Field L] [Field M]
    [Algebra A L] [IsFractionRing A L] [Algebra B M] [IsFractionRing B M]
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (i : L →+* Ω) (j : M →+* Ω)
    (hi : i.comp (algebraMap A L) = f.toRingHom)
    (hj : j.comp (algebraMap B M) = g.toRingHom) (x : Ω) :
    x ∈ AmbientTensorImage f g ↔
      x ∈ i.fieldRange ⊔ j.fieldRange ∧ IsIntegral R x := by
  letI := ambientTensorImage_finite f g
  letI := ambientTensorImage_isIntegralClosure f g
  constructor
  · intro hx
    let a : AmbientTensorImage f g := ⟨x, hx⟩
    have hxrange : x ∈ (ambientTensorFractionEmbedding f g).fieldRange :=
      ⟨algebraMap (AmbientTensorImage f g) (FractionRing (AmbientTensorImage f g)) a,
        ambientTensorFractionAlgebraEmbedding_original f g a⟩
    rw [ambientTensorFractionEmbedding_compositum f g i j hi hj] at hxrange
    exact ⟨hxrange, (IsIntegral.of_finite R a).map (AmbientTensorImage f g).val⟩
  · rintro ⟨hx, hint⟩
    rw [← ambientTensorFractionEmbedding_compositum f g i j hi hj] at hx
    obtain ⟨y, hy⟩ := hx
    have hyint : IsIntegral R y :=
      (isIntegral_algHom_iff (ambientTensorFractionAlgebraEmbedding f g)
        (ambientTensorFractionAlgebraEmbedding f g).injective).mp (by
          change IsIntegral R (ambientTensorFractionEmbedding f g y)
          rw [hy]
          exact hint)
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff
      (A := AmbientTensorImage f g) (R := R)
      (B := FractionRing (AmbientTensorImage f g))).mp hyint
    have hax : (a : Ω) = x := by
      calc
        (a : Ω) = ambientTensorFractionAlgebraEmbedding f g
            (algebraMap (AmbientTensorImage f g) (FractionRing (AmbientTensorImage f g)) a) :=
          (ambientTensorFractionAlgebraEmbedding_original f g a).symm
        _ = ambientTensorFractionAlgebraEmbedding f g y := congrArg _ ha
        _ = x := hy
    exact hax ▸ a.property

end
end Dubon2026
