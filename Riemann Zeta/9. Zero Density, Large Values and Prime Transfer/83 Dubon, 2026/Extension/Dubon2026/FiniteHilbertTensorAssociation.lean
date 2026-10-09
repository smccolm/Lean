import Dubon2026.FiniteHilbertTensorReindex
import Dubon2026.TensorOrbitSpanning
import Mathlib.Algebra.BigOperators.Fin

/-! # Genuine grouping of adjacent finite Hilbert tensor factors -/

namespace Dubon2026

noncomputable section
open scoped TensorProduct

variable {n m : ℕ} (V : Fin (n + m) → ComplexInnerCarrier)

/-- The actual tensor of the original pure vectors in two adjacent finite blocks. -/
def finiteHilbertTensorBlockFamily
    (b : (∀ i : Fin n, V (Fin.castAdd m i)) × (∀ j : Fin m, V (Fin.natAdd n j))) :
    finiteHilbertTensor n (fun i => V (Fin.castAdd m i)) ⊗[ℂ]
      finiteHilbertTensor m (fun j => V (Fin.natAdd n j)) :=
  finiteHilbertPureTensor (fun i => V (Fin.castAdd m i)) b.1 ⊗ₜ[ℂ]
    finiteHilbertPureTensor (fun j => V (Fin.natAdd n j)) b.2

/-- The original two-block pure family spans the entire actual binary tensor of the finite blocks. -/
theorem finiteHilbertTensorBlockFamily_span :
    Submodule.span ℂ (Set.range (finiteHilbertTensorBlockFamily V)) = ⊤ :=
  tensorFamily_span_eq_top (finiteHilbertPureTensor (fun i => V (Fin.castAdd m i)))
    (finiteHilbertPureTensor (fun j => V (Fin.natAdd n j)))
    (finiteHilbertPureTensor_span _) (finiteHilbertPureTensor_span _)

/-- Grouping adjacent actual factors preserves exactly their genuine product Gram matrix. -/
theorem finiteHilbertTensorBlockFamily_gram
    (a b : (∀ i : Fin n, V (Fin.castAdd m i)) × (∀ j : Fin m, V (Fin.natAdd n j))) :
    inner ℂ (finiteHilbertTensorBlockFamily V a) (finiteHilbertTensorBlockFamily V b) =
      inner ℂ (finiteHilbertPureTensor V (Fin.addCases a.1 a.2))
        (finiteHilbertPureTensor V (Fin.addCases b.1 b.2)) := by
  simp only [finiteHilbertTensorBlockFamily, TensorProduct.inner_tmul, finiteHilbertPureTensor_inner,
    Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]

/-- The joined actual pure vectors span the complete genuine finite tensor. -/
theorem finiteHilbertTensorJoinedFamily_span :
    Submodule.span ℂ (Set.range (fun b : (∀ i : Fin n, V (Fin.castAdd m i)) ×
      (∀ j : Fin m, V (Fin.natAdd n j)) => finiteHilbertPureTensor V (Fin.addCases b.1 b.2))) = ⊤ := by
  have he : Set.range (fun b : (∀ i : Fin n, V (Fin.castAdd m i)) × (∀ j : Fin m, V (Fin.natAdd n j)) =>
      finiteHilbertPureTensor V (Fin.addCases b.1 b.2)) = Set.range (finiteHilbertPureTensor V) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨b, rfl⟩
      exact ⟨Fin.addCases b.1 b.2, rfl⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨((fun i => x (Fin.castAdd m i)), (fun j => x (Fin.natAdd n j))), ?_⟩
      exact congrArg (finiteHilbertPureTensor V) (Fin.addCases_castAdd_natAdd x)
  exact (congrArg (Submodule.span ℂ) he).trans (finiteHilbertPureTensor_span V)

/-- The genuine two-block tensor maps isometrically to the original full finite Hilbert tensor. -/
def finiteHilbertTensorAssociation :
    (finiteHilbertTensor n (fun i => V (Fin.castAdd m i)) ⊗[ℂ]
      finiteHilbertTensor m (fun j => V (Fin.natAdd n j))) →ₗᵢ[ℂ] finiteHilbertTensor (n + m) V :=
  gramSpanningIsometry (finiteHilbertTensorBlockFamily V)
    (fun b => finiteHilbertPureTensor V (Fin.addCases b.1 b.2))
    (finiteHilbertTensorBlockFamily_gram V) (finiteHilbertTensorBlockFamily_span V)

/-- The true grouping isometry concatenates exactly the original pure vectors. -/
theorem finiteHilbertTensorAssociation_pure
    (a : ∀ i : Fin n, V (Fin.castAdd m i)) (b : ∀ j : Fin m, V (Fin.natAdd n j)) :
    finiteHilbertTensorAssociation V (finiteHilbertTensorBlockFamily V (a, b)) =
      finiteHilbertPureTensor V (Fin.addCases a b) :=
  gramSpanningIsometry_family _ _ _ _ (a, b)

/-- The actual grouping isometry covers the full genuine finite tensor. -/
theorem finiteHilbertTensorAssociation_range :
    (finiteHilbertTensorAssociation V).toLinearMap.range = ⊤ :=
  (gramSpanningIsometry_range _ _ _ _).trans (finiteHilbertTensorJoinedFamily_span V)

end
end Dubon2026
