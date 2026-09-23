import TaoTrudgianYang2025.SargosQuarticMomentScale

/-! Large-source Robert--Sargos sixth-moment reduction at the faithfully rounded integer scales. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuartic_large_source_sixth_moment :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (Δ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N:ℝ) ≤ Δ → Δ ≤ 1/4 →
      let m := sargosQuarticRoundedDualScale N Δ
      sargosQuarticDyadicSixthMoment N Δ ≤
        C*Δ*(Real.log N)^6*(sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m)) := by
  obtain ⟨K,hK,hsource⟩ := sargosQuartic_source_sixth_integral_bound
  let D := 15728640*sargosWindowConstant 3 1916928
  let E := 128/(Real.log 2)^6
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hCw := sargosWindowConstant_nonneg 3 (by norm_num : (0:ℝ) ≤ 1916928)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hDE : 1 ≤ D+E+1 := by linarith only [hD,hE]
  refine ⟨K*(D+E+1),?_,?_⟩
  · have hh := mul_le_mul hK hDE (by norm_num : (0:ℝ) ≤ 1) hK0
    simpa only [one_mul] using hh
  intro N Δ hN hΔ hΔ₁ m
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hΔp := (sargosQuartic_source_scale hNr hΔ).1
  have hΔhalf : Δ ≤ 1/2 := by linarith only [hΔ₁]
  have hm := sargosQuarticRoundedDualScale_moment_bounds hN hΔ hΔ₁
  change 2 ≤ m ∧ 2 ≤ 2*m ∧ (m:ℝ) ≤ 4*Δ*N ∧ ((2*m:ℕ):ℝ) ≤ 4*Δ*N ∧ 2*m ≤ N at hm
  have hmN : m ≤ N := by omega
  have hmNr : (m:ℝ) ≤ N := by exact_mod_cast hmN
  have hm2Nr : ((2*m:ℕ):ℝ) ≤ N := by exact_mod_cast hm.2.2.2.2
  have ht₁ := sargosQuarticDualSixthIntegral_le_logN hm.1 hNp hΔp hΔhalf hm.2.2.1 hmNr
  have ht₂ := sargosQuarticDualSixthIntegral_le_logN hm.2.1 hNp hΔp hΔhalf hm.2.2.2.1 hm2Nr
  let B := sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m)
  let L := (Real.log (N:ℝ))^6
  let V := D*Δ^4*L*B
  have hI₁ := sargosSixthBaseMoment_nonneg m
  have hI₂ := sargosSixthBaseMoment_nonneg (2*m)
  have hB0 : 0 ≤ B := add_nonneg hI₁ hI₂
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hdual : sargosQuarticDualSixthIntegral m N Δ+sargosQuarticDualSixthIntegral (2*m) N Δ ≤
      ENNReal.ofReal V := by
    apply (add_le_add ht₁ ht₂).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp [V,D,L,B]
    ring
  have hs := hsource N Δ hN hΔ hΔhalf
  change ENNReal.ofReal (sargosQuarticDyadicSixthMoment N Δ) ≤
    ENNReal.ofReal K*(ENNReal.ofReal (1/Δ^3)*
      (sargosQuarticDualSixthIntegral m N Δ+sargosQuarticDualSixthIntegral (2*m) N Δ)+
        ENNReal.ofReal (2*Δ)) at hs
  have hu := hs.trans (mul_le_mul le_rfl
    (add_le_add (mul_le_mul le_rfl hdual bot_le bot_le) le_rfl) bot_le bot_le)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/Δ^3),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity : 0 ≤ 1/Δ^3) hV) (by positivity),
    ← ENNReal.ofReal_mul hK0] at hu
  have hscale : (1/Δ^3)*V = D*Δ*L*B := by
    dsimp [V]
    field_simp
  rw [hscale] at hu
  have hB : 1/64 ≤ B := by
    have hh := sargosSixthBaseMoment_lower (by omega : 1 ≤ m)
    dsimp [B]
    linarith only [hh,hI₂]
  have he := sargos_sixth_log_absorb_error (by linarith only [hNr] : (2:ℝ) ≤ N) hΔp.le hB
  change 2*Δ ≤ E*Δ*L*B at he
  have hinside : D*Δ*L*B+2*Δ ≤ (D+E+1)*Δ*L*B := by
    have hn : 0 ≤ Δ*L*B := by positivity
    nlinarith only [he,hn]
  have hf := hu.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hinside hK0))
  have hfinal : 0 ≤ K*(D+E+1)*Δ*L*B := by positivity
  apply (ENNReal.ofReal_le_ofReal_iff hfinal).mp
  convert hf using 1
  congr 1
  ring

end TaoTrudgianYang2025
