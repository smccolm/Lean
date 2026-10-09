import Dubon2026.FiniteHilbertTensorReindex
import Mathlib.Algebra.BigOperators.Fin

/-! # Genuine finite tensor reference extensions for a directed Hilbert tensor construction -/

namespace Dubon2026

noncomputable section

variable {n : ℕ} (V : Fin (n + 1) → ComplexInnerCarrier)
  (y : V (Fin.last n))

/-- Appending an actual unit reference preserves the original finite product Gram matrix. -/
theorem finiteHilbertReferenceExtension_gram (hy : ‖y‖ = 1)
    (x z : ∀ i : Fin n, V i.castSucc) :
    inner ℂ (finiteHilbertPureTensor (fun i : Fin n => V i.castSucc) x)
      (finiteHilbertPureTensor (fun i : Fin n => V i.castSucc) z) =
      inner ℂ (finiteHilbertPureTensor V (Fin.snoc x y)) (finiteHilbertPureTensor V (Fin.snoc z y)) := by
  rw [finiteHilbertPureTensor_inner, finiteHilbertPureTensor_inner, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, inner_self_eq_norm_sq_to_K, hy]
  norm_num

/-- The genuine isometric extension appends the specified actual unit reference to finite tensors. -/
def finiteHilbertReferenceExtension (hy : ‖y‖ = 1) :
    finiteHilbertTensor n (fun i : Fin n => V i.castSucc) →ₗᵢ[ℂ] finiteHilbertTensor (n + 1) V :=
  gramSpanningIsometry (finiteHilbertPureTensor (fun i : Fin n => V i.castSucc))
    (fun x => finiteHilbertPureTensor V (Fin.snoc x y))
    (finiteHilbertReferenceExtension_gram V y hy) (finiteHilbertPureTensor_span _)

/-- Every actual pure tensor is extended by exactly the original unit reference in the new factor. -/
theorem finiteHilbertReferenceExtension_pure (hy : ‖y‖ = 1) (x : ∀ i : Fin n, V i.castSucc) :
    finiteHilbertReferenceExtension V y hy (finiteHilbertPureTensor (fun i : Fin n => V i.castSucc) x) =
      finiteHilbertPureTensor V (Fin.snoc x y) :=
  gramSpanningIsometry_family _ _ _ _ x

end
end Dubon2026
