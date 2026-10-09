import Dubon2026.GramSpanCompletion

/-! # A genuine completed isometric equivalence from an actual dense Gram identity -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The actual relation-preserving Gram construction and genuine completion identify the two original Hilbert spaces. -/
def gramDenseFamilyEquiv (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (hu : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) : E ≃ₗᵢ[ℂ] F :=
  (gramDenseSpanCompletionEquiv u hu).symm.trans (gramDenseTargetCompletionEquiv u v h hv)

/-- The completed genuine equivalence retains each exact original family vector. -/
theorem gramDenseFamilyEquiv_family (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (hu : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) (i : ι) :
    gramDenseFamilyEquiv u v h hu hv (u i) = v i := by
  let x : Completion (Submodule.span ℂ (Set.range u)) := (gramSpanFamily u i : Submodule.span ℂ (Set.range u))
  have hx : gramDenseSpanCompletionEquiv u hu x = u i :=
    gramDenseSpanCompletionEquiv_coe u hu (gramSpanFamily u i)
  change gramDenseTargetCompletionEquiv u v h hv ((gramDenseSpanCompletionEquiv u hu).symm (u i)) = v i
  rw [← hx, LinearIsometryEquiv.symm_apply_apply]
  exact gramDenseTargetCompletionEquiv_family u v h hv i

/-- Actual bounded operators that act through the same original family reindexing intertwine on the entire original completed spaces. -/
theorem gramDenseFamilyEquiv_intertwines (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (hu : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (τ : ι → ι)
    (hA : ∀ i, A (u i) = u (τ i)) (hB : ∀ i, B (v i) = v (τ i)) (x : E) :
    gramDenseFamilyEquiv u v h hu hv (A x) = B (gramDenseFamilyEquiv u v h hu hv x) := by
  let T := (gramDenseFamilyEquiv u v h hu hv).toLinearIsometry.toContinuousLinearMap
  let L : E →L[ℂ] F := T.comp A - B.comp T
  have hs : Submodule.span ℂ (Set.range u) ≤ LinearMap.ker L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change gramDenseFamilyEquiv u v h hu hv (A (u i)) -
      B (gramDenseFamilyEquiv u v h hu hv (u i)) = 0
    rw [hA, gramDenseFamilyEquiv_family, gramDenseFamilyEquiv_family, hB, sub_self]
  have hx : x ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure := by rw [hu]; trivial
  have hz := closure_minimal hs L.isClosed_ker hx
  exact sub_eq_zero.mp hz

end
end Dubon2026
