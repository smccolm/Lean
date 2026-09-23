import TaoTrudgianYang2025.SargosQuarticMorseSupport
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Whole-line transport and integrable derivatives of the actual cutoff weight. -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem sargosQuartic_integral_eq_global_morse {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (g : ℝ → ℂ) :
    (∫ u : ℝ, (χ u : ℂ)*g u) =
      ∫ z : ℝ, (sargosQuarticMorseWeight χ ε r z : ℂ)*g (sargosQuarticMorseInverse ε r z) := by
  have hsource : (∫ u in Ioo (0 : ℝ) 3, (χ u : ℂ)*g u) =
      ∫ u : ℝ, (χ u : ℂ)*g u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hc : χ u = 0 := image_eq_zero_of_notMem_tsupport (fun h => hu (hs h))
    simp only [hc,Complex.ofReal_zero,zero_mul]
  rw [← hsource,sargosQuartic_integral_Ioo_eq_morseIntegral hε hr,
    ← integral_indicator (sargosQuarticMorseRange_isOpen hε hr).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ sargosQuarticMorseRange ε r
  · rw [Set.indicator_of_mem hz,sargosQuarticMorseWeight_eq hz,
      sargosQuarticMorseAmplitude,Complex.ofReal_mul]
    ring
  · rw [Set.indicator_of_notMem hz,sargosQuarticMorseWeight_zero_of_not_mem hz,
      Complex.ofReal_zero,zero_mul]

theorem sargosQuarticMorseWeight_deriv_support {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (k : ℕ) :
    tsupport (iteratedDeriv k (sargosQuarticMorseWeight χ ε r)) ⊆
      sargosQuarticMorseCoordinate ε r '' tsupport χ := by
  induction k with
  | zero => exact sargosQuarticMorseWeight_tsupport_subset hs hε hr
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem sargosQuarticMorseWeight_iteratedDeriv_integrable {χ : ℝ → ℝ} {ε r : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (k : ℕ) :
    Integrable (iteratedDeriv k (sargosQuarticMorseWeight χ ε r)) := by
  have hc : HasCompactSupport (iteratedDeriv k (sargosQuarticMorseWeight χ ε r)) :=
    (sargosQuarticMorseCoordinate_image_tsupport_isCompact hs hε hr).of_isClosed_subset
      (isClosed_tsupport _) (sargosQuarticMorseWeight_deriv_support hs hε hr k)
  exact ((sargosQuarticMorseWeight_contDiff hχ hs hε hr).continuous_iteratedDeriv k
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).integrable_of_hasCompactSupport hc

end TaoTrudgianYang2025

