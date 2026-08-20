import RiemannZeta.GuthMaynard.HughesYoungMainTerms
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Complex
open scoped Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Holomorphic removal of the zeta pole in the Hughes--Young shifts

Hughes--Young's six main terms must be combined before the shifts are set
to zero.  The basic local coordinate in that combination is
`z * zeta (1 + z)`.  Mathlib assigns a harmless junk value to `zeta 1`, so
the literal product is not the desired extension at `z = 0`.  This file
defines the genuine holomorphic extension from the regular part of the
Hurwitz-zeta continuation and proves its exact punctured-neighbourhood
identity.
-/

/-- The holomorphic regular part of `zeta` at its pole.  The Gamma factor is
kept exactly as in Mathlib's continuation, so the definition is valid at
`s = 1` as well as away from it. -/
noncomputable def riemannZetaRegularPart (s : ℂ) : ℂ :=
  riemannZeta s - (1 / (s - 1)) * (Complex.Gammaℝ s)⁻¹

/-- The regular part is complex differentiable everywhere. -/
theorem differentiable_riemannZetaRegularPart :
    Differentiable ℂ riemannZetaRegularPart := by
  intro s
  by_cases hs : s = 1
  · subst s
    simpa only [riemannZetaRegularPart,
      HurwitzZeta.hurwitzZetaEven_zero] using
      HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div
        (0 : AddCircle (1 : ℝ))
  · unfold riemannZetaRegularPart
    exact (differentiableAt_riemannZeta hs).sub
      (((differentiableAt_const (c := (1 : ℂ))).div
          (differentiableAt_id.sub
            (differentiableAt_const (c := (1 : ℂ))))
          (sub_ne_zero.mpr hs)).mul
        differentiable_Gammaℝ_inv.differentiableAt)

/-- The regular part is entire, in the analytic-function sense used by the
later one-parameter shifted main-term argument. -/
theorem analyticOnNhd_riemannZetaRegularPart :
    AnalyticOnNhd ℂ riemannZetaRegularPart Set.univ :=
  fun z _ ↦ differentiable_riemannZetaRegularPart.analyticAt z

/-- The genuine holomorphic extension of `z * zeta (1 + z)` through
`z = 0`. -/
noncomputable def riemannZetaPoleRemoved (z : ℂ) : ℂ :=
  (Complex.Gammaℝ (1 + z))⁻¹ +
    z * riemannZetaRegularPart (1 + z)

/-- The pole-removed zeta factor is entire. -/
theorem differentiable_riemannZetaPoleRemoved :
    Differentiable ℂ riemannZetaPoleRemoved := by
  unfold riemannZetaPoleRemoved
  exact (differentiable_Gammaℝ_inv.comp
      ((differentiable_const (c := (1 : ℂ))).add differentiable_id)).add
    (differentiable_id.mul
      (differentiable_riemannZetaRegularPart.comp
        ((differentiable_const (c := (1 : ℂ))).add differentiable_id)))

theorem analyticOnNhd_riemannZetaPoleRemoved :
    AnalyticOnNhd ℂ riemannZetaPoleRemoved Set.univ :=
  fun z _ ↦ differentiable_riemannZetaPoleRemoved.analyticAt z

/-- Away from the origin, the extension is exactly the source factor
`z * zeta (1 + z)`. -/
theorem riemannZetaPoleRemoved_eq_mul_riemannZeta
    {z : ℂ} (hz : z ≠ 0) :
    riemannZetaPoleRemoved z = z * riemannZeta (1 + z) := by
  have hsub : (1 + z : ℂ) - 1 = z := by ring
  unfold riemannZetaPoleRemoved riemannZetaRegularPart
  rw [hsub]
  field_simp [hz]
  ring

/-- The extension has the residue-one value at the origin. -/
theorem riemannZetaPoleRemoved_zero :
    riemannZetaPoleRemoved 0 = 1 := by
  simp [riemannZetaPoleRemoved, Complex.Gammaℝ_one]

/-- Affine form used for every polar factor in the one-parameter
Hughes--Young specialization. -/
theorem riemannZeta_one_add_eq_poleRemoved_div
    {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ 0) :
    riemannZeta (1 + a * z) =
      riemannZetaPoleRemoved (a * z) / (a * z) := by
  have haz : a * z ≠ 0 := mul_ne_zero ha hz
  rw [riemannZetaPoleRemoved_eq_mul_riemannZeta haz]
  field_simp [haz]

/-- A uniform local bound for the pole-removed factor.  This is the compact
maximum estimate used after all six shifted terms share one small circle. -/
theorem exists_uniform_norm_riemannZetaPoleRemoved_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖riemannZetaPoleRemoved z‖ ≤ C := by
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    isCompact_closedBall _ _
  obtain ⟨z₀, hz₀, hmax⟩ := hcompact.exists_isMaxOn
    (by exact ⟨0, by simp⟩)
    (differentiable_riemannZetaPoleRemoved.continuous.norm.continuousOn)
  let B : ℝ := max 1 ‖riemannZetaPoleRemoved z₀‖
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact (hmax hzmem).trans (le_max_right _ _)

end RiemannZeta.GuthMaynard
