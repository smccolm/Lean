import Dubon2026.TorusGridApproximation
import Dubon2026.JessenMean

/-! # Finite grid upper bounds for truncated Bohr logarithms -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

theorem eventually_real_torusGridAverage_uniform (N : ℕ) (f : C(PrimeTorus N, ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : PrimeTorus N,
      |(Fintype.card (PrimeCoordinate N → ZMod (n + 1)) : ℝ)⁻¹ *
        (∑ j : PrimeCoordinate N → ZMod (n + 1), f (z + torusGridPoint N (n + 1) j)) -
          (∫ w, f w ∂torusHaar N)| < ε := by
  let g : C(PrimeTorus N, ℂ) := ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  filter_upwards [eventually_torusGridAverage_uniform N g hε] with n hn
  intro z
  have he : torusGridAverage N (n + 1) g z - (∫ w, g w ∂torusHaar N) =
      (((Fintype.card (PrimeCoordinate N → ZMod (n + 1)) : ℝ)⁻¹ *
        (∑ j : PrimeCoordinate N → ZMod (n + 1), f (z + torusGridPoint N (n + 1) j)) -
          (∫ w, f w ∂torusHaar N) : ℝ) : ℂ) := by
    simp only [torusGridAverage, g, ContinuousMap.coe_mk, integral_complex_ofReal,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum]
  simpa only [he, Complex.norm_real, Real.norm_eq_abs] using hn z

theorem eventually_grid_truncated_log_le (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ z : PrimeTorus N,
      (∑ j : PrimeCoordinate N → ZMod (n + 1),
        Real.log (max ‖bohrOnTorus a N σ (z + torusGridPoint N (n + 1) j)‖ ε)) ≤
          (Fintype.card (PrimeCoordinate N → ZMod (n + 1)) : ℝ) *
            ((∫ w, Real.log (max ‖bohrOnTorus a N σ w‖ ε) ∂torusHaar N) + δ) := by
  let f := (truncatedLogNorm ε hε).comp (bohrOnTorus a N σ)
  filter_upwards [eventually_real_torusGridAverage_uniform N f hδ] with n hn
  intro z
  have hc : 0 < (Fintype.card (PrimeCoordinate N → ZMod (n + 1)) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (PrimeCoordinate N → ZMod (n + 1)))
  have hh := (abs_lt.mp (hn z)).2
  change (Fintype.card (PrimeCoordinate N → ZMod (n + 1)) : ℝ)⁻¹ *
    (∑ j : PrimeCoordinate N → ZMod (n + 1),
      Real.log (max ‖bohrOnTorus a N σ (z + torusGridPoint N (n + 1) j)‖ ε)) -
        (∫ w, Real.log (max ‖bohrOnTorus a N σ w‖ ε) ∂torusHaar N) < δ at hh
  apply (inv_mul_le_iff₀ hc).mp
  linarith

end

end Dubon2026
