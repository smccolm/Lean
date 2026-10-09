import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Completion of an actual linear isometry and its exact closed range -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- The actual continuous linear extension of an original isometry to the completion of its domain. -/
def linearIsometryCompletionMap (T : V →ₗᵢ[ℂ] W) : Completion V →L[ℂ] W :=
  T.toContinuousLinearMap.extend (Completion.toComplL : V →L[ℂ] Completion V)

/-- The completed linear map agrees exactly with the original isometry on every original vector. -/
theorem linearIsometryCompletionMap_coe (T : V →ₗᵢ[ℂ] W) (x : V) :
    linearIsometryCompletionMap T (x : Completion V) = T x :=
  ContinuousLinearMap.extend_eq T.toContinuousLinearMap Completion.denseRange_coe
    (Completion.isUniformInducing_coe V) x

/-- The genuine extension preserves the norm of every completed vector. -/
theorem linearIsometryCompletionMap_norm (T : V →ₗᵢ[ℂ] W) (x : Completion V) :
    ‖linearIsometryCompletionMap T x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (linearIsometryCompletionMap T).continuous) continuous_norm
  | ih x => rw [linearIsometryCompletionMap_coe, T.norm_map, Completion.norm_coe]

/-- The genuine extension is a linear isometry on the actual completed domain. -/
def linearIsometryCompletion (T : V →ₗᵢ[ℂ] W) : Completion V →ₗᵢ[ℂ] W where
  toLinearMap := (linearIsometryCompletionMap T).toLinearMap
  norm_map' := linearIsometryCompletionMap_norm T

/-- The completed isometry retains the literal original map on its dense domain. -/
theorem linearIsometryCompletion_coe (T : V →ₗᵢ[ℂ] W) (x : V) :
    linearIsometryCompletion T (x : Completion V) = T x :=
  linearIsometryCompletionMap_coe T x

/-- The range of the actual completed isometry is precisely the closure of the original range. -/
theorem linearIsometryCompletion_range (T : V →ₗᵢ[ℂ] W) :
    (linearIsometryCompletion T).toLinearMap.range = T.toLinearMap.range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Completion.induction_on with
    | hp =>
      exact T.toLinearMap.range.isClosed_topologicalClosure.preimage
        (linearIsometryCompletion T).continuous
    | ih x =>
      change linearIsometryCompletion T (x : Completion V) ∈ T.toLinearMap.range.topologicalClosure
      rw [linearIsometryCompletion_coe]
      exact T.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : Completion V), linearIsometryCompletion_coe T x⟩
    · exact (linearIsometryCompletion T).isometry.isClosedEmbedding.isClosed_range

/-- Intertwining of original bounded operators extends to the actual completed domain. -/
theorem linearIsometryCompletion_intertwines (T : V →ₗᵢ[ℂ] W)
    (A : V →L[ℂ] V) (B : W →L[ℂ] W)
    (h : ∀ x, T (A x) = B (T x)) (x : Completion V) :
    linearIsometryCompletion T (A.completion x) = B (linearIsometryCompletion T x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((linearIsometryCompletion T).continuous.comp A.completion.continuous)
      (B.continuous.comp (linearIsometryCompletion T).continuous)
  | ih x =>
    rw [ContinuousLinearMap.completion_apply_coe, linearIsometryCompletion_coe,
      linearIsometryCompletion_coe]
    exact h x

end
end Dubon2026
