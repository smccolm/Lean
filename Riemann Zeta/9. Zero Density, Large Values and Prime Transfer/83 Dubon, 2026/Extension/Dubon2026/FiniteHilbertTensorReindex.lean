import Dubon2026.FiniteHilbertTensor
import Dubon2026.GramSpanningIsometry

/-! # Genuine isometric reordering of finite Hilbert tensors -/

namespace Dubon2026

noncomputable section

/-- Every tuple of reordered factors is obtained by permuting a tuple of the original factors. -/
theorem forall_reindexed_tuple {n : ℕ} (A : Fin n → Type*) (e : Equiv.Perm (Fin n))
    (P : (∀ i, A (e i)) → Prop) (h : ∀ g : ∀ i, A i, P (fun i => g (e i)))
    (g : ∀ i, A (e i)) : P g := by
  obtain ⟨x, rfl⟩ := (Equiv.piCongrLeft A e).symm.surjective g
  exact h x

/-- All genuine pure tensors span the actual finite algebraic Hilbert tensor. -/
theorem finiteHilbertPureTensor_span {n : ℕ} (V : Fin n → ComplexInnerCarrier) :
    Submodule.span ℂ (Set.range (finiteHilbertPureTensor V)) = ⊤ := by
  exact finiteHilbertPureTensor_family_span V (fun i => V i) (fun _ => id)
    (fun _ => by rw [Set.range_id, Submodule.span_univ])

/-- The actual pure tensor family after reordering its original factors by a genuine permutation. -/
def finiteHilbertReindexedPureFamily {n : ℕ} (V : Fin n → ComplexInnerCarrier) (e : Equiv.Perm (Fin n))
    (x : ∀ i, V i) : finiteHilbertTensor n (fun i => V (e i)) :=
  finiteHilbertPureTensor (fun i => V (e i)) (fun i => x (e i))

/-- Reordering the original vector coordinates retains a spanning family of the genuine reordered tensor space. -/
theorem finiteHilbertReindexedPureFamily_span {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (e : Equiv.Perm (Fin n)) :
    Submodule.span ℂ (Set.range (finiteHilbertReindexedPureFamily V e)) = ⊤ := by
  have h := (Equiv.piCongrLeft (fun i => V i) e).symm.surjective.range_comp
    (finiteHilbertPureTensor (fun i => V (e i)))
  exact (congrArg (Submodule.span ℂ) h).trans (finiteHilbertPureTensor_span (fun i => V (e i)))

/-- The genuine reordered pure tensors have exactly their original finite product Gram matrix. -/
theorem finiteHilbertReindexedPureFamily_gram {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (e : Equiv.Perm (Fin n)) (x y : ∀ i, V i) :
    inner ℂ (finiteHilbertReindexedPureFamily V e x) (finiteHilbertReindexedPureFamily V e y) =
      inner ℂ (finiteHilbertPureTensor V x) (finiteHilbertPureTensor V y) := by
  rw [finiteHilbertReindexedPureFamily, finiteHilbertReindexedPureFamily,
    finiteHilbertPureTensor_inner, finiteHilbertPureTensor_inner]
  exact Equiv.prod_comp e (fun i => inner ℂ (x i) (y i))

/-- A genuine isometry reorders the original finite Hilbert tensor factors and their actual pure vectors. -/
def finiteHilbertTensorReindexIsometry {n : ℕ} (V : Fin n → ComplexInnerCarrier) (e : Equiv.Perm (Fin n)) :
    finiteHilbertTensor n (fun i => V (e i)) →ₗᵢ[ℂ] finiteHilbertTensor n V :=
  gramSpanningIsometry (finiteHilbertReindexedPureFamily V e) (finiteHilbertPureTensor V)
    (finiteHilbertReindexedPureFamily_gram V e) (finiteHilbertReindexedPureFamily_span V e)

/-- The actual tensor reordering sends every reordered original pure tensor to exactly its original tensor. -/
theorem finiteHilbertTensorReindexIsometry_pure {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (e : Equiv.Perm (Fin n)) (x : ∀ i, V i) :
    finiteHilbertTensorReindexIsometry V e (finiteHilbertReindexedPureFamily V e x) =
      finiteHilbertPureTensor V x :=
  gramSpanningIsometry_family _ _ _ _ x

/-- The genuine tensor reordering is onto the entire original finite tensor space. -/
theorem finiteHilbertTensorReindexIsometry_range {n : ℕ} (V : Fin n → ComplexInnerCarrier)
    (e : Equiv.Perm (Fin n)) : (finiteHilbertTensorReindexIsometry V e).toLinearMap.range = ⊤ :=
  (gramSpanningIsometry_range _ _ _ _).trans (finiteHilbertPureTensor_span V)

/-- Reordering actual finite Hilbert tensor factors is a genuine linear isometry equivalence. -/
def finiteHilbertTensorReindexEquiv {n : ℕ} (V : Fin n → ComplexInnerCarrier) (e : Equiv.Perm (Fin n)) :
    finiteHilbertTensor n (fun i => V (e i)) ≃ₗᵢ[ℂ] finiteHilbertTensor n V :=
  (finiteHilbertTensorReindexIsometry V e).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ (finiteHilbertTensorReindexIsometry_range V e))

end
end Dubon2026
