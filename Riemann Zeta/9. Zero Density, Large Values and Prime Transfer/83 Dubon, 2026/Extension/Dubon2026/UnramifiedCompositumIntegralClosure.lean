import Dubon2026.TensorCompositumIntegralClosure

/-! # Actual integral closures in finite unramified field composita -/

namespace Dubon2026

noncomputable section

variable {R A B Ω : Type*} [CommRing R] [CommRing A] [CommRing B] [Field Ω]
  [Algebra R A] [Algebra R B] [Algebra R Ω]
  [IsDedekindDomain R] [Module.Finite R A] [Module.Finite R B]
  [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified R B]
  {L M : Type*} [Field L] [Field M]
  [Algebra A L] [IsFractionRing A L] [Algebra B M] [IsFractionRing B M]

/-- If the original fraction-field images generate the actual ambient field, their genuine tensor image is the integral closure there. -/
theorem ambientTensorImage_isIntegralClosure_of_compositum_top
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (i : L →+* Ω) (j : M →+* Ω)
    (hi : i.comp (algebraMap A L) = f.toRingHom)
    (hj : j.comp (algebraMap B M) = g.toRingHom)
    (htop : i.fieldRange ⊔ j.fieldRange = ⊤) :
    IsIntegralClosure (AmbientTensorImage f g) R Ω where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      have hmem : x ∈ AmbientTensorImage f g :=
        (ambientTensorImage_mem_iff_compositum_integral f g i j hi hj x).mpr
          ⟨by rw [htop]; trivial, hx⟩
      exact ⟨⟨x, hmem⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ((ambientTensorImage_mem_iff_compositum_integral
        f g i j hi hj (y : Ω)).mp y.property).2

/-- The actual integral closure in the original field compositum is formally unramified when the two original finite algebras are formally unramified. -/
theorem integralClosure_formallyUnramified_of_compositum_top
    (f : A →ₐ[R] Ω) (g : B →ₐ[R] Ω) (i : L →+* Ω) (j : M →+* Ω)
    (hi : i.comp (algebraMap A L) = f.toRingHom)
    (hj : j.comp (algebraMap B M) = g.toRingHom)
    (htop : i.fieldRange ⊔ j.fieldRange = ⊤)
    (C : Type*) [CommRing C] [Algebra R C] [Algebra C Ω]
    [IsScalarTower R C Ω] [IsIntegralClosure C R Ω] :
    Algebra.FormallyUnramified R C := by
  letI := ambientTensorImage_isIntegralClosure_of_compositum_top f g i j hi hj htop
  letI := ambientTensorImage_formallyUnramified f g
  exact Algebra.FormallyUnramified.of_equiv
    (IsIntegralClosure.equiv R (AmbientTensorImage f g) Ω C)

end
end Dubon2026
