import TaoTrudgianYang2025.SargosQuarticBoundedScale

/-! The omitted bounded source range, using actual moment comparison and diagonal lower bounds. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuarticDyadicSixthMoment_le_base (N : ℕ) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hΔ₁ : Δ ≤ 1/2) :
    sargosQuarticDyadicSixthMoment N Δ ≤ sargosSixthBaseMoment N := by
  exact sargosQuartic_power_rectangle_mono N 6 (fun _ => 1) hΔ
    (by linarith only [hΔ₁]) le_rfl le_rfl

theorem sargosQuartic_bounded_source_sixth_moment {N : ℕ} {Δ : ℝ}
    (hN : 16 ≤ N) (hN₁ : N ≤ 9216)
    (hΔ : 1/Real.sqrt (N:ℝ) ≤ Δ) (hΔ₁ : Δ ≤ 1/4) :
    let m := sargosQuarticRoundedDualScale N Δ
    sargosQuarticDyadicSixthMoment N Δ ≤
      (96*(9216:ℝ)^3*(128/(Real.log 2)^6))*Δ*(Real.log N)^6*
        (sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m)) := by
  intro m
  have hNr : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hNup : (N:ℝ) ≤ 9216 := by exact_mod_cast hN₁
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hs := sargosQuartic_source_scale_sixteen hNr hΔ
  have hsmall := sargosQuartic_bounded_source_delta hNp hNup hΔ
  have hm : 1 ≤ m := by change 1 ≤ sargosQuarticRoundedDualScale N Δ; omega
  have hI := sargosSixthBaseMoment_lower hm
  have hI₂ := sargosSixthBaseMoment_nonneg (2*m)
  have hB : 1/64 ≤ sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m) := by
    linarith only [hI,hI₂]
  have herr := sargos_sixth_log_absorb_error
    (by linarith only [hNr] : (2:ℝ) ≤ N) hs.1.le hB
  have hbase := (sargosQuarticDyadicSixthMoment_le_base N hs.1.le
    (by linarith only [hΔ₁])).trans
      (sargosSixthBaseMoment_trivial (by omega : 1 ≤ N))
  have hp := pow_le_pow_left₀ hNp.le hNup 3
  have hdelta : 1 ≤ 96*Δ := by linarith only [hsmall]
  have hscale := mul_le_mul_of_nonneg_left hdelta (by norm_num : (0:ℝ) ≤ 2*9216^3)
  have hsource : sargosQuarticDyadicSixthMoment N Δ ≤ (96*(9216:ℝ)^3)*(2*Δ) := by
    nlinarith only [hbase,hp,hscale]
  apply hsource.trans
  exact (mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 96*9216^3)).trans_eq (by ring)

theorem sargosQuartic_sixth_moment_reduction :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (Δ : ℝ),
      16 ≤ N → 1/Real.sqrt (N:ℝ) ≤ Δ → Δ ≤ 1/4 →
      let m := sargosQuarticRoundedDualScale N Δ
      sargosQuarticDyadicSixthMoment N Δ ≤
        C*Δ*(Real.log N)^6*(sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m)) := by
  obtain ⟨C,hC,hlarge⟩ := sargosQuartic_large_source_sixth_moment
  let D := 96*(9216:ℝ)^3*(128/(Real.log 2)^6)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C+D,by linarith only [hC,hD],?_⟩
  intro N Δ hN hΔ hΔ₁ m
  have hNr : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hΔp := (sargosQuartic_source_scale_sixteen hNr hΔ).1
  have hB : 0 ≤ sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m) :=
    add_nonneg (sargosSixthBaseMoment_nonneg m) (sargosSixthBaseMoment_nonneg (2*m))
  have hfactor : 0 ≤ Δ*(Real.log N)^6*
      (sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m)) := by positivity
  by_cases hbig : 9216 ≤ N
  · have hh := hlarge N Δ hbig hΔ hΔ₁
    apply hh.trans
    have hc : C ≤ C+D := by linarith only [hD]
    convert mul_le_mul_of_nonneg_right hc hfactor using 1 <;> ring
  · have hh := sargosQuartic_bounded_source_sixth_moment hN (by omega) hΔ hΔ₁
    apply hh.trans
    have hc : D ≤ C+D := by linarith only [hC]
    convert mul_le_mul_of_nonneg_right hc hfactor using 1 <;> ring

end TaoTrudgianYang2025
