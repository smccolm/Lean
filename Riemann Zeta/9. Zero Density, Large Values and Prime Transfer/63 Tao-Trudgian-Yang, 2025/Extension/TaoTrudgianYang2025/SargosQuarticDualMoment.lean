import TaoTrudgianYang2025.SargosQuarticCoverMoment

/-! The source-linked dual sixth moment after its actual parameter transfer and finite cover. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuarticDual_sixth_moment {M : ℕ}
    (hM : 2 ≤ M) {N Δ : ℝ} (hN : 0 < N) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2)
    (hscale : (M:ℝ) ≤ 4*Δ*N) :
    (∫⁻ α in Icc Δ (2*Δ), ∫⁻ γ in Icc (-(1/N^3)) (1/N^3),
      ENNReal.ofReal ((sargosSlowQuarticMaximum M (fun _ => 1)
        (1/(4*α)) (-γ/(16*α^4)) (fun t => γ^2*t^6/(16*α^7)))^6)) ≤
      ENNReal.ofReal (15728640*sargosWindowConstant 3 1916928*Δ^4*
        (Real.log M)^6*sargosSixthBaseMoment M) := by
  have ht := sargosQuarticDual_sixth_parameter_transfer M hN hΔ
  have hc := sargosQuarticSextic_cover_moment hM hN hΔ hΔ₁ hscale
  have he : (1/N^3)/(16*Δ^4) = sargosQuarticParameterHeight N Δ := by
    unfold sargosQuarticParameterHeight
    ring
  simp only [neg_div,he] at ht ⊢
  apply ht.trans
  apply (mul_le_mul (le_refl (ENNReal.ofReal (4096*Δ^6))) hc bot_le bot_le).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4096*Δ^6)]
  apply le_of_eq
  congr 1
  field_simp
  ring

theorem sargosQuarticRoundedDualScale_moment_bounds {N : ℕ} {Δ : ℝ}
    (hN : 9216 ≤ N) (hΔ : 1/Real.sqrt (N:ℝ) ≤ Δ) (hΔ₁ : Δ ≤ 1/4) :
    let m := sargosQuarticRoundedDualScale N Δ
    2 ≤ m ∧ 2 ≤ 2*m ∧ (m:ℝ) ≤ 4*Δ*N ∧ ((2*m:ℕ):ℝ) ≤ 4*Δ*N ∧ 2*m ≤ N := by
  intro m
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hs := sargosQuarticRoundedDualScale_bounds hNr hΔ
  have hp := (sargosQuartic_source_scale hNr hΔ).1
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hm : (m:ℝ) ≤ 2*Δ*N := hs.2.1
  have hm2 : ((2*m:ℕ):ℝ) ≤ 4*Δ*N := by
    push_cast
    linarith only [hm]
  have hscale : 4*Δ*(N:ℝ) ≤ N := by
    have hh := mul_le_mul_of_nonneg_right hΔ₁ hNp.le
    nlinarith only [hh]
  have hnat : 2*m ≤ N := by exact_mod_cast hm2.trans hscale
  refine ⟨by change 2 ≤ sargosQuarticRoundedDualScale N Δ; omega,by omega,?_,hm2,hnat⟩
  have hn := mul_nonneg hp.le hNp.le
  nlinarith only [hm,hn]

end TaoTrudgianYang2025
