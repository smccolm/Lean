import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! DUB-17/18 -> residual primitive realization -> the integral Tate
image spans the same coefficient space as its rational scalar extension.
Native pure tensors and linearity prove this directly; no compact-image
or separately supplied spanning-lattice theorem is needed. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct
variable {R K M V : Type*} [CommRing R] [CommRing K] [Algebra R K]
variable [AddCommGroup M] [Module R M] [AddCommGroup V] [Module K V]
variable [Module R V] [IsScalarTower R K V]

/-- Restrict a rationalized map to the original integral vectors. -/
def scalarExtensionIntegralMap (π : K ⊗[R] M →ₗ[K] V) : M →ₗ[R] V :=
  (π.restrictScalars R).comp (TensorProduct.mk R K M 1)

theorem scalarExtensionIntegralMap_tmul (π : K ⊗[R] M →ₗ[K] V) (c : K) (x : M) :
    π (c ⊗ₜ[R] x) = c • scalarExtensionIntegralMap π x := by
  have h : c ⊗ₜ[R] x = c • (1 ⊗ₜ[R] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg π h).trans (π.map_smul c (1 ⊗ₜ[R] x))

theorem scalarExtensionIntegralMap_span {E : Type*} [CommRing E] [Algebra K E]
    [Module E V] [IsScalarTower K E V] (π : K ⊗[R] M →ₗ[K] V) :
    Submodule.span E (Set.range π) = Submodule.span E (Set.range (scalarExtensionIntegralMap π)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c x =>
      rw [scalarExtensionIntegralMap_tmul]
      exact (Submodule.span E (Set.range (scalarExtensionIntegralMap π))).restrictScalars K
        |>.smul_mem c (Submodule.subset_span ⟨x, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[R] x, rfl⟩

theorem scalarExtensionIntegralMap_intertwines
    (π : K ⊗[R] M →ₗ[K] V) (u : V → V) (r : M →ₗ[R] M)
    (he : ∀ z, u (π z) = π (r.baseChange K z)) (x : M) :
    u (scalarExtensionIntegralMap π x) = scalarExtensionIntegralMap π (r x) :=
  he (1 ⊗ₜ[R] x)

end
end Dubon2026
