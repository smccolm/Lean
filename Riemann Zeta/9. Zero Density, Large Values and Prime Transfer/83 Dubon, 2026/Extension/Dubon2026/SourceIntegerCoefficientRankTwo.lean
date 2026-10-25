import Dubon2026.SourceRankTwoBaseChange
import Dubon2026.SourceIntegerCoefficientEndExtension

/-! DUB-17/18 -> primitive determinant -> the actual primitive Tate image.
The original integral-action coordinate identity extends to every element
of the literal arithmetic coefficient tensor algebra. -/
namespace Dubon2026
noncomputable section
open TensorProduct
variable {F K E T A V : Type*} [Field F] [Field K] [Field E] [CommRing T] [Ring A]
variable [Algebra K E] [Algebra K T] [AddCommGroup V] [Module K V]

theorem integerCoefficient_rankTwo_coordinates
    (τ : F →+* E) (θ : A →+* Module.End K V) (δ : A →+* T)
    (e : V ≃ₗ[K] (Fin 2 → T))
    (h : ∀ (t : A) (v : V), e (θ t v) = fun i => δ t * e v i)
    (z : F ⊗[ℤ] A) (x : E ⊗[K] V) (i : Fin 2) :
    rankTwoBaseChangeEquiv e
      (integerCoefficientEndExtension τ
        ((Module.End.baseChangeHom K E V).toRingHom.comp θ) z x) i =
      integerCoefficientExtension τ
        ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := T)).toRingHom.comp δ) z *
        rankTwoBaseChangeEquiv e x i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have hθ : integerCoefficientEndExtension τ
        ((Module.End.baseChangeHom K E V).toRingHom.comp θ) (a ⊗ₜ[ℤ] t) =
          τ a • (θ t).baseChange E := rfl
    have hδ : integerCoefficientExtension τ
        ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := T)).toRingHom.comp δ)
          (a ⊗ₜ[ℤ] t) = τ a • ((1 : E) ⊗ₜ[K] δ t) := rfl
    rw [hθ, hδ]
    simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply,
      rankTwoBaseChangeEquiv_operator e (θ t) (δ t) (h t), smul_mul_assoc]
  | add z w hz hw =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hz, hw, add_mul]

theorem exists_integerCoefficient_rankTwo_coordinates
    (τ : F →+* E) (θ : A →+* Module.End K V) (δ : A →+* T)
    (he : ∃ e : V ≃ₗ[K] (Fin 2 → T),
      ∀ (t : A) (v : V), e (θ t v) = fun i => δ t * e v i) :
    ∃ e : E ⊗[K] V ≃ₗ[E] (Fin 2 → E ⊗[K] T),
      ∀ (z : F ⊗[ℤ] A) (x : E ⊗[K] V) (i : Fin 2),
        e (integerCoefficientEndExtension τ
          ((Module.End.baseChangeHom K E V).toRingHom.comp θ) z x) i =
        integerCoefficientExtension τ
          ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := T)).toRingHom.comp δ) z *
          e x i := by
  obtain ⟨e, he⟩ := he
  exact ⟨rankTwoBaseChangeEquiv e, integerCoefficient_rankTwo_coordinates τ θ δ e he⟩

end
end Dubon2026
