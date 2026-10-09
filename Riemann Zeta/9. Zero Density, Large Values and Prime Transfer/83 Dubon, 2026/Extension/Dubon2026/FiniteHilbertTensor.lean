import Dubon2026.TensorOrbitSpanning
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! # Finite Hilbert tensors with the genuine recursively inherited tensor inner product -/

namespace Dubon2026

noncomputable section
open scoped TensorProduct

/-- A bundled complex inner-product space, used only to carry the actual structures through finite tensor recursion. -/
structure ComplexInnerCarrier where
  /-- The actual underlying vector space. -/
  carrier : Type
  /-- Its actual normed additive group. -/
  normed : NormedAddCommGroup carrier
  /-- Its actual complex inner product. -/
  innerSpace : @InnerProductSpace ℂ carrier inferInstance normed.toSeminormedAddCommGroup

instance : CoeSort ComplexInnerCarrier Type := ⟨ComplexInnerCarrier.carrier⟩
instance (V : ComplexInnerCarrier) : NormedAddCommGroup V := V.normed
instance (V : ComplexInnerCarrier) : InnerProductSpace ℂ V := V.innerSpace

/-- Bundle an already given genuine complex inner-product space. -/
def ComplexInnerCarrier.of (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : ComplexInnerCarrier :=
  ⟨V, inferInstance, inferInstance⟩

/-- The genuine binary algebraic Hilbert tensor, retaining Mathlib's proved positive definite product inner product. -/
def ComplexInnerCarrier.tensor (V W : ComplexInnerCarrier) : ComplexInnerCarrier :=
  ComplexInnerCarrier.of (V ⊗[ℂ] W)

/-- The finite algebraic Hilbert tensor is an iterated genuine binary tensor; its zero-factor unit is the scalar field. -/
def finiteHilbertTensor : (n : ℕ) → (Fin n → ComplexInnerCarrier) → ComplexInnerCarrier
  | 0, _ => ComplexInnerCarrier.of ℂ
  | n + 1, V => (V 0).tensor (finiteHilbertTensor n (fun i => V i.succ))

/-- The actual pure tensor of a finite family of original vectors. -/
def finiteHilbertPureTensor : {n : ℕ} → (V : Fin n → ComplexInnerCarrier) →
    (∀ i, V i) → finiteHilbertTensor n V
  | 0, _, _ => (1 : ℂ)
  | n + 1, V, x => (x 0) ⊗ₜ[ℂ] finiteHilbertPureTensor (fun i : Fin n => V i.succ) (fun i => x i.succ)

/-- The genuine finite tensor inner product is precisely the product of the original factor inner products. -/
theorem finiteHilbertPureTensor_inner {n : ℕ} (V : Fin n → ComplexInnerCarrier) (x y : ∀ i, V i) :
    inner ℂ (finiteHilbertPureTensor V x) (finiteHilbertPureTensor V y) =
      ∏ i, inner ℂ (x i) (y i) := by
  induction n with
  | zero =>
    change inner ℂ (1 : ℂ) (1 : ℂ) = ∏ i : Fin 0, inner ℂ (x i) (y i)
    simp
  | succ n ih =>
    change inner ℂ (x 0 ⊗ₜ[ℂ] finiteHilbertPureTensor (fun i : Fin n => V i.succ) (fun i => x i.succ))
      (y 0 ⊗ₜ[ℂ] finiteHilbertPureTensor (fun i : Fin n => V i.succ) (fun i => y i.succ)) = _
    rw [TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]

/-- The genuine finite pure-tensor norm is the product of the original factor norms. -/
theorem finiteHilbertPureTensor_norm {n : ℕ} (V : Fin n → ComplexInnerCarrier) (x : ∀ i, V i) :
    ‖finiteHilbertPureTensor V x‖ = ∏ i, ‖x i‖ := by
  induction n with
  | zero =>
    change ‖(1 : ℂ)‖ = ∏ i : Fin 0, ‖x i‖
    simp
  | succ n ih =>
    change ‖x 0 ⊗ₜ[ℂ] finiteHilbertPureTensor (fun i : Fin n => V i.succ) (fun i => x i.succ)‖ = _
    rw [TensorProduct.norm_tmul, ih, Fin.prod_univ_succ]

/-- Genuine pure tensors of spanning factor families span the entire finite algebraic Hilbert tensor. -/
theorem finiteHilbertPureTensor_family_span {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (I : Fin n → Type) (u : ∀ i, I i → V i)
    (hu : ∀ i, Submodule.span ℂ (Set.range (u i)) = ⊤) :
    Submodule.span ℂ (Set.range (fun g : ∀ i, I i => finiteHilbertPureTensor V (fun i => u i (g i)))) = ⊤ := by
  induction n with
  | zero =>
    change Submodule.span ℂ (Set.range (fun _ : ∀ i : Fin 0, I i => (1 : ℂ))) = ⊤
    apply top_unique
    intro z _
    have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (fun _ : ∀ i : Fin 0, I i => (1 : ℂ))) :=
      Submodule.subset_span ⟨fun i => Fin.elim0 i, rfl⟩
    simpa only [smul_eq_mul, mul_one] using Submodule.smul_mem
      (Submodule.span ℂ (Set.range (fun _ : ∀ i : Fin 0, I i => (1 : ℂ)))) z h
  | succ n ih =>
    have ht := tensorFamily_span_eq_top (u 0)
      (fun g : ∀ i : Fin n, I i.succ =>
        finiteHilbertPureTensor (fun i : Fin n => V i.succ) (fun i => u i.succ (g i)))
      (hu 0) (ih (fun i => V i.succ) (fun i => I i.succ) (fun i => u i.succ) (fun i => hu i.succ))
    change Submodule.span ℂ (Set.range (fun g : ∀ i, I i =>
      u 0 (g 0) ⊗ₜ[ℂ] finiteHilbertPureTensor (fun i : Fin n => V i.succ)
        (fun i => u i.succ (g i.succ)))) = ⊤
    apply top_unique
    rw [← ht]
    apply Submodule.span_mono
    rintro _ ⟨⟨g, gs⟩, rfl⟩
    exact ⟨Fin.cons g gs, rfl⟩

end
end Dubon2026
