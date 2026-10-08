import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Derivatives through the actual closed isometric realization of a complete space -/

namespace Dubon2026

noncomputable section
open Filter
open scoped Topology

/-- A derivative of an isometrically realized curve lies in the actual closed image of its complete original space. -/
theorem derivative_mem_linearIsometry_range {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (c : ℝ → E) {D : F}
    (h : HasDerivAt (fun t => e (c t)) D 0) : D ∈ Set.range e := by
  apply e.isometry.isClosedEmbedding.isClosed_range.mem_of_tendsto h.tendsto_slope_zero
  apply Eventually.of_forall
  intro t
  refine ⟨t⁻¹ • (c (0 + t) - c 0), ?_⟩
  simp only [map_smul, map_sub]

/-- Differentiability of the original realized curve lifts to its complete original space, with no separately assumed derivative vector. -/
theorem differentiableAt_of_linearIsometry_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (c : ℝ → E)
    (h : DifferentiableAt ℝ (fun t => e (c t)) 0) : DifferentiableAt ℝ c 0 := by
  obtain ⟨v, hv⟩ := derivative_mem_linearIsometry_range e c h.hasDerivAt
  have hd : HasDerivAt c v 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    apply e.isometry.isEmbedding.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, map_smul, map_sub, hv] using h.hasDerivAt.tendsto_slope_zero
  exact hd.differentiableAt

end
end Dubon2026
