import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! DUB-17/18 -> raw reciprocity -> invariant simple-pole residue in a cell.
A nonsingular analytic change of coordinate preserves the simple-pole residue.
Native divided power series supply analytic divided differences, so the
remainder is constructed explicitly. This is the analytic part of the actual
original-differential residue consumer in the next module.
Adapted from S_AlgebraicCurve_coeffIn_local_calculus, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open Filter
open scoped Topology

theorem analyticAt_dslope {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (dslope f z₀) z₀ := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem exists_simple_pole_pullback_remainder (σ G₀ : ℂ → ℂ) (w₀ r : ℂ)
    (hσa : AnalyticAt ℂ σ w₀) (hσ0 : σ w₀ = 0) (hσd : deriv σ w₀ ≠ 0)
    (hG₀a : AnalyticAt ℂ G₀ 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G w₀ ∧ ∀ᶠ w in 𝓝[≠] w₀,
      (r / σ w + G₀ (σ w)) * deriv σ w = r / (w - w₀) + G w := by
  let κ := dslope σ w₀
  have hκa : AnalyticAt ℂ κ w₀ := analyticAt_dslope hσa
  have hκ0 : κ w₀ ≠ 0 := by rw [show κ w₀ = deriv σ w₀ from dslope_same _ _]; exact hσd
  have hκw : ∀ w, σ w = (w - w₀) * κ w := by
    intro w
    have h := sub_smul_dslope σ w₀ w
    simpa only [smul_eq_mul, hσ0, sub_zero] using h.symm
  let q : ℂ → ℂ := fun w => deriv σ w / κ w
  have hqa : AnalyticAt ℂ q w₀ := hσa.deriv.div hκa hκ0
  have hq1 : q w₀ = 1 := by
    dsimp only [q, κ]
    rw [dslope_same, div_self hσd]
  let m := dslope q w₀
  have hma : AnalyticAt ℂ m w₀ := analyticAt_dslope hqa
  have hmw : ∀ w, q w = 1 + (w - w₀) * m w := by
    intro w
    have h := sub_smul_dslope q w₀ w
    rw [smul_eq_mul, hq1] at h
    change q w = 1 + (w - w₀) * dslope q w₀ w
    rw [h]
    ring
  refine ⟨fun w => r * m w + G₀ (σ w) * deriv σ w,
    (analyticAt_const.mul hma).add ((hG₀a.comp_of_eq hσa hσ0).mul hσa.deriv), ?_⟩
  have hκne := hκa.continuousAt.eventually_ne hκ0
  filter_upwards [hκne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hκwn hwne
  have hwn : w - w₀ ≠ 0 := sub_ne_zero.mpr hwne
  have hq' : deriv σ w = q w * κ w := by
    dsimp only [q]
    field_simp
  have hdiv : r / σ w * deriv σ w = r / (w - w₀) + r * m w := by
    rw [hκw w, hq', hmw w]
    field_simp
  rw [add_mul]
  linear_combination hdiv

end
end Dubon2026.SourceFunctionField.CellGeometry
