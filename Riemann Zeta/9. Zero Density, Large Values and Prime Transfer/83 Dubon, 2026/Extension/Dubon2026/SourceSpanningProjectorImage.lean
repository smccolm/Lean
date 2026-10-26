import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! DUB-17/18 -> primitive determinant -> compare the actual nondegenerate
projector image with the existing spanning primitive specialization.
Native scalar-extension range and finite-dimensional bijectivity retain
the original specialization map, with no replacement representation. -/
namespace Dubon2026
noncomputable section
variable {K E V W : Type*} [Field K] [Field E] [Algebra K E]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module E W] [Module K W] [IsScalarTower K E W]

theorem spanning_liftBaseChange_surjective (π : V →ₗ[K] W)
    (hspan : Submodule.span E (Set.range π) = ⊤) :
    Function.Surjective (π.liftBaseChange E) := by
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_liftBaseChange]
  exact hspan

variable {U : Type*} [AddCommGroup U] [Module E U]

theorem projector_range_specialization_surjective (π : U →ₗ[E] W)
    (Q : Module.End E U) (hπ : Function.Surjective π)
    (hQ : ∀ x, π (Q x) = π x) :
    Function.Surjective (π.comp Q.range.subtype) := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  exact ⟨⟨Q x, LinearMap.mem_range_self Q x⟩, hQ x⟩

theorem projector_range_specialization_bijective [FiniteDimensional E W]
    (π : U →ₗ[E] W) (Q : Module.End E U) (hπ : Function.Surjective π)
    (hQ : ∀ x, π (Q x) = π x) (e : Q.range ≃ₗ[E] W) :
    Function.Bijective (π.comp Q.range.subtype) := by
  letI : FiniteDimensional E Q.range := Module.Finite.of_injective e.toLinearMap e.injective
  have hs := projector_range_specialization_surjective π Q hπ hQ
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank e.finrank_eq).mpr hs, hs⟩

/-- Restrict the already prescribed specialization to the actual projector image. -/
def projectorRangeSpecializationEquiv [FiniteDimensional E W]
    (π : U →ₗ[E] W) (Q : Module.End E U) (hπ : Function.Surjective π)
    (hQ : ∀ x, π (Q x) = π x) (e : Q.range ≃ₗ[E] W) : Q.range ≃ₗ[E] W :=
  LinearEquiv.ofBijective (π.comp Q.range.subtype)
    (projector_range_specialization_bijective π Q hπ hQ e)

end
end Dubon2026
