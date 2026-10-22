import Mathlib.Analysis.RCLike.Extend
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Tactic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> full real
span of actual loop periods. Native extension of real functionals gives
the complex coefficients needed for the period annihilator argument.
Native open mapping makes an analytic function locally constant at a
local maximum of its real part. These are exactly the two real-analytic
inputs to the compact original-curve consumer.
The maximum-principle argument is adapted from
S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.PeriodRealDual
noncomputable section
open Filter Set Metric
open scoped Topology

/-- Coefficients of the native complex extension of a real functional. -/
def coefficients {n : ℕ} (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ) (i : Fin n) : ℂ :=
  Module.Dual.extendRCLike ℓ (Pi.single i 1)

theorem apply_eq_re_sum {n : ℕ} (ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ) (w : Fin n → ℂ) :
    ℓ w = (∑ i, coefficients ℓ i * w i).re := by
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
    ext j
    simp [Pi.single_apply]
  calc
    ℓ w = (Module.Dual.extendRCLike ℓ w : ℂ).re :=
      (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) ℓ w).symm
    _ = (∑ i, coefficients ℓ i * w i).re := by
      congr 1
      conv_lhs => rw [hw]
      simp only [map_sum, map_smul, smul_eq_mul, coefficients, mul_comm]

theorem eventually_eq_of_isLocalMax_re {Φ : ℂ → ℂ} {z₀ : ℂ}
    (hΦ : AnalyticAt ℂ Φ z₀) (hmax : IsLocalMax (fun z => (Φ z).re) z₀) :
    ∀ᶠ z in 𝓝 z₀, Φ z = Φ z₀ := by
  rcases hΦ.eventually_constant_or_nhds_le_map_nhds with h | h
  · exact h
  · exfalso
    have hmem : {w : ℂ | w.re ≤ (Φ z₀).re} ∈ 𝓝 (Φ z₀) := h (Filter.mem_map.mpr hmax)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
    have hin : Φ z₀ + ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (Φ z₀) ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have hle := hball hin
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, add_le_iff_nonpos_right] at hle
    linarith

end
end Dubon2026.SourceFunctionField.PeriodRealDual
