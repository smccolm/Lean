import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! DUB-17/18 -> original torsion cardinality -> complex Abel--Jacobi
comparison -> elliptic place charts -> descent of an invariant analytic
germ through its ramified power coordinate. Native open mapping transfers
continuity through the power map. Away from zero its nonzero derivative
transfers analyticity, and native removable singularities finish at zero.
This avoids new power-series compression or algebraic convergence theory.
The actual invariant original-place consumer remains the next step.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Filter
open scoped Topology

theorem analyticAt_of_comp_power (n : ℕ) (hn : n ≠ 0) (F : ℂ → ℂ)
    (h : AnalyticAt ℂ (fun z : ℂ => F (z ^ n)) 0) : AnalyticAt ℂ F 0 := by
  letI : NeZero n := ⟨hn⟩
  have hmap : map (fun z : ℂ => z ^ n) (𝓝 (0 : ℂ)) = 𝓝 (0 : ℂ) := by
    simpa only [zero_pow hn] using (Complex.isOpenQuotientMap_pow n).map_nhds_eq 0
  have hc : ContinuousAt F 0 := by
    change map F (𝓝 (0 : ℂ)) ≤ 𝓝 (F 0)
    rw [← hmap, Filter.map_map]
    simpa only [Function.comp_apply, zero_pow hn] using h.continuousAt.tendsto
  have himage : (fun z : ℂ => z ^ n) ''
      {z | AnalyticAt ℂ (fun w : ℂ => F (w ^ n)) z} ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]
    change ∀ᶠ z in 𝓝 (0 : ℂ), z ^ n ∈ (fun w : ℂ => w ^ n) ''
      {w | AnalyticAt ℂ (fun u : ℂ => F (u ^ n)) w}
    filter_upwards [h.eventually_analyticAt] with z hz
    exact ⟨z, hz, rfl⟩
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hc
  filter_upwards [mem_nhdsWithin_of_mem_nhds himage, self_mem_nhdsWithin] with z hz hz0
  obtain ⟨u, hu, rfl⟩ := hz
  have hu0 : u ≠ 0 := by
    intro he
    exact hz0 (by simp only [he, zero_pow hn, Set.mem_singleton_iff])
  have hp : AnalyticAt ℂ (fun w : ℂ => w ^ n) u := analyticAt_id.pow n
  have hpd : deriv (fun w : ℂ => w ^ n) u ≠ 0 := by
    rw [(hasDerivAt_pow n u).deriv]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hu0)
  exact ((analyticAt_comp_iff_of_deriv_ne_zero hp hpd).mp hu).differentiableAt

end
end Dubon2026.SourceFunctionField
