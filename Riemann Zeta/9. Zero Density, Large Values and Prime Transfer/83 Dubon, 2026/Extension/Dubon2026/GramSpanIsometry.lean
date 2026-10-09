import Dubon2026.GramSpanningIsometry

/-! # The original Gram isometry on the literal span of a family -/

namespace Dubon2026

noncomputable section

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The original family as actual vectors in its own algebraic span. -/
def gramSpanFamily (u : ι → E) (i : ι) : Submodule.span ℂ (Set.range u) :=
  ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩

/-- The actual family spans its own original algebraic span as a module. -/
theorem gramSpanFamily_span (u : ι → E) :
    Submodule.span ℂ (Set.range (gramSpanFamily u)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (Submodule.span ℂ (Set.range u))
    (fun i => Submodule.subset_span (Set.mem_range_self i))).mpr rfl

/-- A proved Gram identity defines the faithful linear isometry on the literal original span. -/
def gramSpanIsometry (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    Submodule.span ℂ (Set.range u) →ₗᵢ[ℂ] F :=
  gramSpanningIsometry (gramSpanFamily u) v h (gramSpanFamily_span u)

/-- The faithful original-span isometry retains the exact given family correspondence. -/
theorem gramSpanIsometry_family (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) (i : ι) :
    gramSpanIsometry u v h (gramSpanFamily u i) = v i :=
  gramSpanningIsometry_family (gramSpanFamily u) v h (gramSpanFamily_span u) i

/-- The range is exactly the literal span of the second original family. -/
theorem gramSpanIsometry_range (u : ι → E) (v : ι → F)
    (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j)) :
    (gramSpanIsometry u v h).toLinearMap.range = Submodule.span ℂ (Set.range v) :=
  gramSpanningIsometry_range (gramSpanFamily u) v h (gramSpanFamily_span u)

end
end Dubon2026
