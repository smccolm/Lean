import Dubon2026.SourceCurveCompletionNorm
import Dubon2026.SourceCurvePoleProjection

/-! Completion does not change the space of finite principal parts. Density
gives surjectivity, and preservation of integrality gives injectivity.
This identifies the finite-rank residue calculation before and after
completion, a necessary input to DUB-17/18 global residue vanishing. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open scoped Valued

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The actual field embedding into the completion as a map over the constants. -/
def completionLinearMap : F →ₗ[K] v.adicCompletion :=
  (IsScalarTower.toAlgHom K F v.adicCompletion).toLinearMap

/-- Every completed element differs from an original element by an integral one. -/
theorem completion_principalPart_approximation (x : v.adicCompletion) :
    ∃ a : F, x - algebraMap F v.adicCompletion a ∈ v.adicCompletionIntegers := by
  letI := v.completionRankOne
  obtain ⟨a, ha⟩ := (v.heightOneSpectrum.denseRange_algebraMap F).exists_dist_lt x zero_lt_one
  refine ⟨a, ?_⟩
  change Valued.v (x - algebraMap F v.adicCompletion a) ≤ 1
  apply le_of_lt
  rw [← Valued.toNormedField.norm_lt_one_iff]
  simpa only [dist_eq_norm] using ha

/-- The actual map of principal-part spaces induced by completion. -/
def completionPrincipalPartsMap : (F ⧸ v.integralFunctions) →ₗ[K]
    (v.adicCompletion ⧸ v.completionPlace.integralFunctions) :=
  v.integralFunctions.mapQ v.completionPlace.integralFunctions v.completionLinearMap
    (fun x hx => (v.completion_integer_iff x).mpr hx)

/-- The quotient map sends an original element to its completed principal-part class. -/
theorem completionPrincipalPartsMap_mkQ (x : F) :
    v.completionPrincipalPartsMap (v.integralFunctions.mkQ x) =
      v.completionPlace.integralFunctions.mkQ (algebraMap F v.adicCompletion x) := rfl

/-- Completion induces a bijection on principal parts. -/
theorem completionPrincipalPartsMap_bijective : Function.Bijective v.completionPrincipalPartsMap := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := v.integralFunctions.mkQ_surjective z
      change v.completionPrincipalPartsMap (v.integralFunctions.mkQ x) = 0 at hz
      rw [v.completionPrincipalPartsMap_mkQ] at hz
      have hx := (Submodule.Quotient.mk_eq_zero _).mp hz
      have hxi := (v.completion_integer_iff x).mp hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr hxi
    · exact bot_le
  · intro z
    obtain ⟨x, rfl⟩ := v.completionPlace.integralFunctions.mkQ_surjective z
    obtain ⟨a, ha⟩ := v.completion_principalPart_approximation x
    refine ⟨v.integralFunctions.mkQ a, ?_⟩
    rw [v.completionPrincipalPartsMap_mkQ, ← sub_eq_zero, ← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa only [neg_sub] using neg_mem ha

/-- The actual linear equivalence between original and completed principal parts. -/
def completionPrincipalPartsEquiv : (F ⧸ v.integralFunctions) ≃ₗ[K]
    (v.adicCompletion ⧸ v.completionPlace.integralFunctions) :=
  LinearEquiv.ofBijective v.completionPrincipalPartsMap v.completionPrincipalPartsMap_bijective

end Dubon2026.SourceCurve.Place
