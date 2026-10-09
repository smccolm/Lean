import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Span.Basic

/-! # Genuine isometric tensor inclusions using unit reference vectors -/

namespace Dubon2026

noncomputable section
open scoped TensorProduct

variable {V W H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Tensoring on the right with an actual unit vector preserves the Hilbert tensor norm. -/
def tensorUnitRight (e : W) (he : ‖e‖ = 1) : V →ₗᵢ[ℂ] V ⊗[ℂ] W where
  toLinearMap := (TensorProduct.mk ℂ V W).flip e
  norm_map' x := by change ‖x ⊗ₜ[ℂ] e‖ = ‖x‖; rw [TensorProduct.norm_tmul, he, mul_one]

/-- Tensoring on the left with an actual unit vector preserves the Hilbert tensor norm. -/
def tensorUnitLeft (e : V) (he : ‖e‖ = 1) : W →ₗᵢ[ℂ] V ⊗[ℂ] W where
  toLinearMap := TensorProduct.mk ℂ V W e
  norm_map' x := by change ‖e ⊗ₜ[ℂ] x‖ = ‖x‖; rw [TensorProduct.norm_tmul, he, one_mul]

/-- The right reference inclusion is literally the original pure tensor. -/
theorem tensorUnitRight_apply (e : W) (he : ‖e‖ = 1) (x : V) :
    tensorUnitRight e he x = x ⊗ₜ[ℂ] e := rfl

/-- The left reference inclusion is literally the original pure tensor. -/
theorem tensorUnitLeft_apply (e : V) (he : ‖e‖ = 1) (x : W) :
    tensorUnitLeft e he x = e ⊗ₜ[ℂ] x := rfl

/-- Exact cancellation of the original normalization in a tensor map. -/
theorem tensorMap_inverse_scalar_references (T : (V ⊗[ℂ] W) →ₗ[ℂ] H)
    (x : V) (y : W) (z : H) (c : ℂ) (hc : c ≠ 0)
    (h : T (x ⊗ₜ[ℂ] y) = c • z) :
    T ((c⁻¹ • x) ⊗ₜ[ℂ] (c⁻¹ • y)) = c⁻¹ • z := by
  rw [TensorProduct.smul_tmul_smul, map_smul, h, smul_smul,
    mul_assoc, inv_mul_cancel₀ hc, mul_one]

/-- Equality on a genuine spanning family determines a linear map on every vector. -/
theorem linearMap_eq_of_spanning_family {I : Type*} (u : I → V)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (T S : V →ₗ[ℂ] H)
    (h : ∀ i, T (u i) = S (u i)) : T = S := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top T S hu).mpr
  rintro ⟨_, i, rfl⟩
  exact h i

/-- A scaled tensor-orbit identity on a spanning family determines the right reference map on the whole factor. -/
theorem tensorMap_right_inverse_reference {I : Type*} (u : I → V)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (T : (V ⊗[ℂ] W) →ₗ[ℂ] H)
    (S : V →ₗ[ℂ] H) (y : W) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ i, T (u i ⊗ₜ[ℂ] y) = c • S (u i)) (x : V) :
    T (x ⊗ₜ[ℂ] (c⁻¹ • y)) = S x := by
  have he : T.comp ((TensorProduct.mk ℂ V W).flip (c⁻¹ • y)) = S := by
    apply linearMap_eq_of_spanning_family u hu
    intro i
    change T (u i ⊗ₜ[ℂ] (c⁻¹ • y)) = S (u i)
    rw [TensorProduct.tmul_smul, map_smul, h, inv_smul_smul₀ hc]
  exact DFunLike.congr_fun he x

/-- A scaled tensor-orbit identity on a spanning family determines the left reference map on the whole factor. -/
theorem tensorMap_left_inverse_reference {I : Type*} (u : I → W)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (T : (V ⊗[ℂ] W) →ₗ[ℂ] H)
    (S : W →ₗ[ℂ] H) (y : V) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ i, T (y ⊗ₜ[ℂ] u i) = c • S (u i)) (x : W) :
    T ((c⁻¹ • y) ⊗ₜ[ℂ] x) = S x := by
  have he : T.comp (TensorProduct.mk ℂ V W (c⁻¹ • y)) = S := by
    apply linearMap_eq_of_spanning_family u hu
    intro i
    change T ((c⁻¹ • y) ⊗ₜ[ℂ] u i) = S (u i)
    rw [← TensorProduct.smul_tmul', map_smul, h, inv_smul_smul₀ hc]
  exact DFunLike.congr_fun he x

end
end Dubon2026
