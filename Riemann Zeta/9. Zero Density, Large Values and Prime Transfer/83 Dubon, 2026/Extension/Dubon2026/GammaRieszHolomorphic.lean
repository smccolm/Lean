import Dubon2026.GammaRieszSymbol
import GuthMaynardExternal.PNT.ResidueCalcOnRectangles

/-! # Holomorphy of the actual Riesz Gamma integrand on the contour-shift strip -/

namespace Dubon2026

open Complex Set MeasureTheory RiemannZeta.GuthMaynard

noncomputable section

/-- The actual complex Mellin integrand whose vertical restrictions define the Riesz Gamma kernels. -/
def gammaRieszMellinFunction (k r x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * gammaRieszSymbol k r s

/-- Every genuine Gamma argument stays in its positive half-plane on this open contour-shift strip. -/
theorem gammaRiesz_gamma_arguments_pos {k r : ℝ} {s : ℂ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hs0 : -(1 / 4 : ℝ) < s.re) (hs1 : s.re < 1) :
    0 < (1 - s).re ∧ 0 < ((k : ℂ) - s).re ∧
      0 < (s + ((r + 1 : ℝ) : ℂ)).re ∧ 0 < (s + ((k - 1 : ℝ) : ℂ)).re := by
  simp only [sub_re, add_re, one_re, ofReal_re]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The actual complex Riesz Gamma Mellin integrand is differentiable throughout the shift strip. -/
theorem differentiableAt_gammaRieszMellinFunction {k r x : ℝ} {s : ℂ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hx : 0 < x)
    (hs0 : -(1 / 4 : ℝ) < s.re) (hs1 : s.re < 1) :
    DifferentiableAt ℂ (gammaRieszMellinFunction k r x) s := by
  obtain ⟨h1, h2, h3, h4⟩ := gammaRiesz_gamma_arguments_pos hk hr hs0 hs1
  have hG1 : DifferentiableAt ℂ (fun z : ℂ => Gamma (1 - z)) s :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos h1).differentiableAt.comp s (by fun_prop)
  have hG2 : DifferentiableAt ℂ (fun z : ℂ => Gamma ((k : ℂ) - z)) s :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos h2).differentiableAt.comp s (by fun_prop)
  have hG3 : DifferentiableAt ℂ (fun z : ℂ => Gamma (z + ((r + 1 : ℝ) : ℂ))) s :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos h3).differentiableAt.comp s (by fun_prop)
  have hG4 : DifferentiableAt ℂ (fun z : ℂ => Gamma (z + ((k - 1 : ℝ) : ℂ))) s :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos h4).differentiableAt.comp s (by fun_prop)
  have hp : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact hp.mul ((hG1.mul hG2).div (hG3.mul hG4)
    (mul_ne_zero (Gamma_ne_zero_of_re_pos h3) (Gamma_ne_zero_of_re_pos h4)))

/-- The full actual Mellin function is holomorphic on the open strip used to move the Riesz contours. -/
theorem differentiableOn_gammaRieszMellinFunction {k r x : ℝ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hx : 0 < x) :
    DifferentiableOn ℂ (gammaRieszMellinFunction k r x) {s : ℂ | -(1 / 4 : ℝ) < s.re ∧ s.re < 1} :=
  fun _ hs => (differentiableAt_gammaRieszMellinFunction hk hr hx hs.1 hs.2).differentiableWithinAt

/-- Cauchy's theorem applies to the literal Riesz Gamma integrand on every finite shift rectangle. -/
theorem gammaRieszMellin_rectangle_eq_zero {k r x β β' T : ℝ}
    (hk : 2 ≤ k) (hr : 0 ≤ r) (hx : 0 < x)
    (hβ0 : -(1 / 4 : ℝ) < β) (hβ : β ≤ β') (hβ1 : β' < 1) (hT : 0 ≤ T) :
    RectangleIntegral (gammaRieszMellinFunction k r x)
      (gammaVerticalPoint β (-T)) (gammaVerticalPoint β' T) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle (differentiableOn_gammaRieszMellinFunction hk hr hx)
  intro s hs
  have hre : (gammaVerticalPoint β (-T)).re ≤ (gammaVerticalPoint β' T).re := by
    simpa only [gammaVerticalPoint_re] using hβ
  have him : (gammaVerticalPoint β (-T)).im ≤ (gammaVerticalPoint β' T).im := by
    simp only [gammaVerticalPoint_im]
    linarith
  have hm := (mem_Rect hre him s).mp hs
  have hlo : β ≤ s.re := by simpa only [gammaVerticalPoint_re] using hm.1
  have hhi : s.re ≤ β' := by simpa only [gammaVerticalPoint_re] using hm.2.1
  exact ⟨hβ0.trans_le hlo, hhi.trans_lt hβ1⟩

end
end Dubon2026
