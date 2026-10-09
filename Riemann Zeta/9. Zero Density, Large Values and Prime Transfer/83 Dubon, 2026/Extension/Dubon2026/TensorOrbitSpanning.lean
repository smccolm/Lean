import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Actual tensor products are spanned by tensors of original generating families -/

namespace Dubon2026

noncomputable section
open scoped TensorProduct

/-- Actual tensors of two genuinely spanning original families span their complete algebraic tensor product. -/
theorem tensorFamily_span_eq_top {ι κ E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (u : ι → E) (v : κ → F)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range (fun a : ι × κ => u a.1 ⊗ₜ[ℂ] v a.2)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun a : ι × κ => u a.1 ⊗ₜ[ℂ] v a.2))
  have hxy (x : E) (y : F) : x ⊗ₜ[ℂ] y ∈ S := by
    have hx : x ∈ Submodule.span ℂ (Set.range u) := hu.symm ▸ Submodule.mem_top
    have hy : y ∈ Submodule.span ℂ (Set.range v) := hv.symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨j, rfl⟩ := hy
            exact Submodule.subset_span ⟨(i, j), rfl⟩
        | zero => simpa only [TensorProduct.tmul_zero] using S.zero_mem
        | add x y hx hy ihx ihy =>
            simpa only [TensorProduct.tmul_add] using S.add_mem ihx ihy
        | smul c x hx ih =>
            simpa only [TensorProduct.tmul_smul] using S.smul_mem c ih
    | zero => simpa only [TensorProduct.zero_tmul] using S.zero_mem
    | add x z hx hz ihx ihz =>
        simpa only [TensorProduct.add_tmul] using S.add_mem ihx ihz
    | smul c x hx ih =>
        simpa only [TensorProduct.smul_tmul'] using S.smul_mem c ih
  apply top_unique
  intro x hx
  clear hx
  change x ∈ S
  induction x using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul x y => exact hxy x y
  | add x y hx hy => exact S.add_mem hx hy

/-- Multiplication by the original generator norm turns the genuine mixed Gram factor into the tensor-product inner product normalization. -/
theorem norm_smul_inner_factor {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (y x z : V) :
    inner ℂ ((‖y‖ : ℂ) • x) ((‖y‖ : ℂ) • z) = inner ℂ x z * inner ℂ y y := by
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [Complex.conj_ofReal]
  rw [pow_two]
  ac_rfl

end
end Dubon2026
