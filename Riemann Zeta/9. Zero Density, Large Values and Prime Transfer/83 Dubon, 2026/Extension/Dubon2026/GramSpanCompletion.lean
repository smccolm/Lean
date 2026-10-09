import Dubon2026.GramSpanIsometry
import Dubon2026.LinearIsometryCompletion

/-! # Completion of the actual dense family spans and their genuine Gram isometries -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Completion of the original span inclusion has exactly the closure of the original span as its range. -/
theorem gramSpanCompletionInclusion_range (u : ι → E) :
    (linearIsometryCompletion (Submodule.span ℂ (Set.range u)).subtypeₗᵢ).toLinearMap.range =
      (Submodule.span ℂ (Set.range u)).topologicalClosure := by
  rw [linearIsometryCompletion_range]
  have he : (Submodule.span ℂ (Set.range u)).subtypeₗᵢ.toLinearMap.range =
      Submodule.span ℂ (Set.range u) := Submodule.range_subtype _
  exact congrArg Submodule.topologicalClosure he

/-- The actual completion of a genuinely dense span is the original complete Hilbert space. -/
def gramDenseSpanCompletionEquiv (u : ι → E)
    (hu : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤) :
    Completion (Submodule.span ℂ (Set.range u)) ≃ₗᵢ[ℂ] E :=
  (linearIsometryCompletion (Submodule.span ℂ (Set.range u)).subtypeₗᵢ).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ ((gramSpanCompletionInclusion_range u).trans hu))

/-- The completed dense-span equivalence sends each original vector to its literal original ambient vector. -/
theorem gramDenseSpanCompletionEquiv_coe (u : ι → E)
    (hu : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (x : Submodule.span ℂ (Set.range u)) :
    gramDenseSpanCompletionEquiv u hu (x : Completion (Submodule.span ℂ (Set.range u))) = x.val :=
  linearIsometryCompletion_coe _ x

omit [CompleteSpace E] in
/-- The completed actual Gram isometry has precisely the original second span closure as its range. -/
theorem gramSpanIsometryCompletion_range (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (linearIsometryCompletion (gramSpanIsometry u v h)).toLinearMap.range =
      (Submodule.span ℂ (Set.range v)).topologicalClosure := by
  rw [linearIsometryCompletion_range, gramSpanIsometry_range]

/-- Completion of the genuine original Gram map gives an equivalence to the complete second space when the actual second family is dense. -/
def gramDenseTargetCompletionEquiv (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    Completion (Submodule.span ℂ (Set.range u)) ≃ₗᵢ[ℂ] F :=
  (linearIsometryCompletion (gramSpanIsometry u v h)).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ ((gramSpanIsometryCompletion_range u v h).trans hv))

omit [CompleteSpace E] in
/-- The completed target equivalence retains the exact original correspondence on all family vectors. -/
theorem gramDenseTargetCompletionEquiv_family (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) (i : ι) :
    gramDenseTargetCompletionEquiv u v h hv
      ((gramSpanFamily u i : Submodule.span ℂ (Set.range u)) : Completion (Submodule.span ℂ (Set.range u))) = v i :=
  (linearIsometryCompletion_coe (gramSpanIsometry u v h) (gramSpanFamily u i)).trans
    (gramSpanIsometry_family u v h i)

end
end Dubon2026
