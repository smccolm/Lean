import RiemannZeta.GuthMaynard.DFIBesselTransformBridge

open Complex Set MeasureTheory
namespace RiemannZeta.GuthMaynard

theorem probe_Y_symbol_ratio (w : ℂ) :
    dfiBesselY0MellinSymbol (2 * w) =
      -(2 / Real.pi : ℂ) * Complex.cos (Real.pi * w) *
        dfiBesselK0MellinSymbol (2 * w) := by
  rw [dfiBesselY0MellinSymbol_two_mul,
    dfiBesselK0MellinSymbol_two_mul]
  have h2 : (2 : ℂ) ^ (2 * w - 1) =
      2 * (2 : ℂ) ^ (2 * w - 2) := by
    calc
      (2 : ℂ) ^ (2 * w - 1) =
          (2 : ℂ) ^ ((1 : ℂ) + (2 * w - 2)) := by congr 1; ring
      _ = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (2 * w - 2) := by
        rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      _ = 2 * (2 : ℂ) ^ (2 * w - 2) := by simp
  rw [h2]
  ring

theorem probe_minus_multiplier_eq_Y_symbol
    (q n : ℕ) [NeZero q] (hn : 0 < n) (z : ℂ)
    (hz : 0 < (1 - z).re) :
    (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z =
      (-(2 * Real.pi) / (q : ℂ)) *
        (2 * ((4 * Real.pi * Real.sqrt n / q : ℝ) : ℂ) ^
          (-(2 * (1 - z))) * dfiBesselY0MellinSymbol (2 * (1 - z))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPlus := dfiVoronoiPlusMultiplier_eq_scaled_K0_mellin q n hn z hz
  rw [mellin_dfiBesselK0_mul_sqrt
    (by positivity : 0 < 4 * Real.pi * Real.sqrt n / q) hz] at hPlus
  have hRatio := probe_Y_symbol_ratio (1 - z)
  have hCos :
      cexp (Real.pi * I * (1 - z)) + cexp (-Real.pi * I * (1 - z)) =
        2 * Complex.cos (Real.pi * (1 - z)) := by
    unfold Complex.cos
    ring_nf
  have hLeft :
      (n : ℂ) ^ (-(1 - z)) * dfiVoronoiMinusMultiplier q z =
        ((n : ℂ) ^ (-(1 - z)) * dfiVoronoiPlusMultiplier q z) *
          Complex.cos (Real.pi * (1 - z)) := by
    unfold dfiVoronoiMinusMultiplier dfiVoronoiPlusMultiplier
    rw [hCos]
    ring
  have hRight :
      (-(2 * Real.pi) / (q : ℂ)) *
          (2 * ((4 * Real.pi * Real.sqrt n / q : ℝ) : ℂ) ^
            (-(2 * (1 - z))) * dfiBesselY0MellinSymbol (2 * (1 - z))) =
        ((4 / (q : ℂ)) *
          (2 * ((4 * Real.pi * Real.sqrt n / q : ℝ) : ℂ) ^
            (-(2 * (1 - z))) * dfiBesselK0MellinSymbol (2 * (1 - z)))) *
          Complex.cos (Real.pi * (1 - z)) := by
    rw [hRatio]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  rw [hLeft, hPlus]
  exact hRight.symm

end RiemannZeta.GuthMaynard
