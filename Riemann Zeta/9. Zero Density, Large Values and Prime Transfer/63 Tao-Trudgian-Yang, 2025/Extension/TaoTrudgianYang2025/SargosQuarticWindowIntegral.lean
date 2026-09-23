import TaoTrudgianYang2025.SargosQuarticCenteredPhase

/-! Exact central-window transport by the actual quartic inverse and positive Jacobian. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem sargosQuartic_integral_inverse_window {ε r H : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hH : 0 ≤ H)
    (hs : Icc (-H) H ⊆ sargosQuarticMorseRange ε r)
    {g : ℝ → ℂ} (hg : ContinuousOn g (Ioo (0 : ℝ) 3)) :
    (∫ u in sargosQuarticMorseInverse ε r (-H)..sargosQuarticMorseInverse ε r H, g u) =
      ∫ z in (-H)..H, ((deriv (sargosQuarticMorseInverse ε r) z : ℝ) : ℂ)*
        g (sargosQuarticMorseInverse ε r z) := by
  have hs' : uIcc (-H) H ⊆ sargosQuarticMorseRange ε r := by
    rwa [uIcc_of_le (by linarith : -H ≤ H)]
  have hd : ∀ z ∈ uIcc (-H) H, HasDerivAt (sargosQuarticMorseInverse ε r)
      (deriv (sargosQuarticMorseInverse ε r) z) z :=
    fun z hz => (sargosQuarticMorseInverse_hasStrictDerivAt hε hr (hs' hz)).hasDerivAt
      |>.differentiableAt.hasDerivAt
  have hc : ContinuousOn (deriv (sargosQuarticMorseInverse ε r)) (uIcc (-H) H) := by
    intro z hz
    exact ((sargosQuarticMorseInverse_contDiffAt hε hr (hs' hz)).derivWithin (m := ∞)
      (by simp)).continuousAt.continuousWithinAt
  have hi : sargosQuarticMorseInverse ε r '' uIcc (-H) H ⊆ Ioo (0 : ℝ) 3 := by
    rintro u ⟨z,hz,rfl⟩
    exact sargosQuarticMorseInverse_mem hε hr (hs' hz)
  have he := intervalIntegral.integral_deriv_smul_comp' hd hc (hg.mono hi)
  simpa only [Function.comp_def,Complex.real_smul] using he.symm

theorem sargosQuarticCentered_window_integral {χ : ℝ → ℝ} {ε r H : ℝ}
    (hχ : Continuous χ) (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hH : 0 ≤ H)
    (hs : Icc (-H) H ⊆ sargosQuarticMorseRange ε r) (T : ℝ) :
    (∫ u in sargosQuarticMorseInverse ε r (-H)..sargosQuarticMorseInverse ε r H,
      (χ u : ℂ)*(𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)) =
      (𝐞 (T*sargosQuarticCenteredPhase ε r r) : ℂ)*
        ∫ z in (-H)..H, (sargosQuarticMorseWeight χ ε r z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ) := by
  have hp : Continuous (fun u => T*sargosQuarticCenteredPhase ε r u) :=
    continuous_const.mul (sargosQuarticCenteredPhase_contDiff ε r).continuous
  have hc : Continuous (fun u : ℝ => (χ u : ℂ)*
      (𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)) :=
    (Complex.continuous_ofReal.comp hχ).mul
      ((continuous_subtype_val.comp Real.continuous_fourierChar).comp hp)
  rw [sargosQuartic_integral_inverse_window hε hr hH hs hc.continuousOn,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z hz
  have hz' : z ∈ sargosQuarticMorseRange ε r := by
    apply hs
    simpa only [uIcc_of_le (by linarith : -H ≤ H)] using hz
  have hform : T*sargosQuarticCenteredPhase ε r (sargosQuarticMorseInverse ε r z) =
      T*sargosQuarticCenteredPhase ε r r+(T/2)*z^2 := by
    rw [sargosQuarticCenteredPhase_inverse hε hr hz']
    ring
  dsimp only
  rw [sargosQuarticMorseWeight_eq hz',sargosQuarticMorseAmplitude,hform,
    AddChar.map_add_eq_mul,Circle.coe_mul,Complex.ofReal_mul]
  ring

end TaoTrudgianYang2025
