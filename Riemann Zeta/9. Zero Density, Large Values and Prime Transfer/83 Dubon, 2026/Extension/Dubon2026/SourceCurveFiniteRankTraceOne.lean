import Dubon2026.SourceCurveFiniteRankTrace

/-! The rank-one trace calculation needed to identify the local commutator
residue with the existing normalized simple-pole residue. The ambient vector
space can be infinite; the calculation takes place in the span of one vector. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The image of a rank-one endomorphism lies in the span of its defining vector. -/
theorem range_smulRight_le_span (χ : V →ₗ[K] K) (e : V) :
    LinearMap.range (χ.smulRight e) ≤ Submodule.span K {e} := by
  rintro x ⟨y, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))

/-- A rank-one operator has finite-dimensional image without a finite ambient-space hypothesis. -/
theorem finite_range_smulRight (χ : V →ₗ[K] K) (e : V) :
    FiniteDimensional K (LinearMap.range (χ.smulRight e)) :=
  Submodule.finiteDimensional_of_le (range_smulRight_le_span χ e)

/-- The actual finite-rank trace of `x ↦ χ(x)e` is `χ(e)`. -/
theorem finrankTrace_smulRight (χ : V →ₗ[K] K) (e : V) :
    haveI := finite_range_smulRight χ e
    finrankTrace (χ.smulRight e) = χ e := by
  haveI := finite_range_smulRight χ e
  let W : Submodule K V := Submodule.span K {e}
  let eW : W := ⟨e, Submodule.subset_span (Set.mem_singleton e)⟩
  have hW : ∀ x ∈ W, (χ.smulRight e) x ∈ W :=
    fun x _ => Submodule.smul_mem _ _ eW.2
  rw [finrankTrace_eq_trace_on_superspace (χ.smulRight e) W
    (range_smulRight_le_span χ e) hW]
  have h : (χ.smulRight e).restrict hW = (χ.domRestrict W).smulRight eW := by
    ext
    rfl
  rw [h, LinearMap.trace_smulRight]
  rfl

end Dubon2026.SourceCurve.ResidueTrace
