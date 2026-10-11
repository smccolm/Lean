import Mathlib.RingTheory.Flat.Equalizer

/-! # Actual tensor images detected by original kernel retractions -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R M N P U : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [AddCommGroup U] [Module R U]

/-- Tensoring an actual kernel retraction fixes every original tensor killed by the tensored map. The existing flat-kernel theorem supplies its true kernel-coordinate preimage. -/
theorem tensorKernelRetraction_fixed [Module.Flat R M]
    (f : N →ₗ[R] P) (p : N →ₗ[R] LinearMap.ker f)
    (hp : p.comp (LinearMap.ker f).subtype = LinearMap.id)
    (z : M ⊗[R] N) (hz : f.lTensor M z = 0) :
    ((LinearMap.ker f).subtype.comp p).lTensor M z = z := by
  have hmem : z ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor R M f) := hz
  rw [Module.Flat.ker_lTensor_eq] at hmem
  obtain ⟨w, rfl⟩ := hmem
  have h : (((LinearMap.ker f).subtype.comp p).lTensor M).comp
      ((LinearMap.ker f).subtype.lTensor M) =
        (LinearMap.ker f).subtype.lTensor M := by
    apply TensorProduct.ext'
    intro m x
    change m ⊗ₜ[R] ((p x.val).val) = m ⊗ₜ[R] x.val
    exact congrArg (fun y : LinearMap.ker f => m ⊗ₜ[R] y.val)
      (LinearMap.congr_fun hp x)
  exact LinearMap.congr_fun h w

/-- The same tensor-kernel argument applies to an original submodule identified with the literal kernel. -/
theorem tensorSubmoduleRetraction_fixed [Module.Flat R M]
    (S : Submodule R N) (f : N →ₗ[R] P) (hS : S = LinearMap.ker f)
    (p : N →ₗ[R] S) (hp : p.comp S.subtype = LinearMap.id)
    (z : M ⊗[R] N) (hz : f.lTensor M z = 0) :
    (S.subtype.comp p).lTensor M z = z := by
  subst S
  exact tensorKernelRetraction_fixed f p hp z hz

/-- Two actual one-factor retraction identities place an original tensor in the image of the tensor of the original coordinate inclusions, with its explicit preimage. -/
theorem tensorRetraction_pair_image (i : U →ₗ[R] M) (p : M →ₗ[R] U)
    (z : M ⊗[R] M)
    (hleft : TensorProduct.map (i.comp p) (LinearMap.id : M →ₗ[R] M) z = z)
    (hright : TensorProduct.map (LinearMap.id : M →ₗ[R] M) (i.comp p) z = z) :
    TensorProduct.map i i (TensorProduct.map p p z) = z := by
  have h : (TensorProduct.map i i).comp (TensorProduct.map p p) =
      (TensorProduct.map (i.comp p) (LinearMap.id : M →ₗ[R] M)).comp
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M) (i.comp p)) := by
    apply TensorProduct.ext'
    intro a b
    rfl
  calc
    _ = TensorProduct.map (i.comp p) (LinearMap.id : M →ₗ[R] M)
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M) (i.comp p) z) :=
      LinearMap.congr_fun h z
    _ = z := by rw [hright, hleft]

end
end Dubon2026
