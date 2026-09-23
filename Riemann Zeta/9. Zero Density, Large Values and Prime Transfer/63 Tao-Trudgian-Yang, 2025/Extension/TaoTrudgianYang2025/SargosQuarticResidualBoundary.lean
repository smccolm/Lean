import TaoTrudgianYang2025.SargosQuarticResidualVariation

/-! Residual variation on the full closed stationary range, with explicit boundary jumps. -/

noncomputable section

open Set
open scoped BigOperators FourierTransform

namespace TaoTrudgianYang2025

theorem finiteVariationBound_sargosQuarticLegendreRemainder_closed
    {N α γ : ℝ} (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (a : ℝ) (L : ℕ)
    (hr : ∀ i : ℕ, i ≤ L → a+i ∈
      Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    FiniteVariationBound (fun i => (𝐞 (sargosQuarticLegendreRemainder N α γ (a+i)) : ℂ))
      L (5+81920*Real.pi) := by
  classical
  have hNp : 0 < N := by linarith
  have hαp := (sargosQuartic_source_scale hN hα).1
  have hγs := sargosQuartic_source_smallness hN hα hγ
  let c := 32768*Real.pi/(α*N)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hL : (L : ℝ) ≤ 5*α*N/2 := by
    have hl := hr 0 (Nat.zero_le L)
    have hu := hr L le_rfl
    have hg := sargosQuarticSlope_gap_upper hNp hαp hγs
      (show N ∈ Icc N (2*N) by constructor <;> linarith)
      (show 2*N ∈ Icc N (2*N) by constructor <;> linarith) (by linarith)
    simp only [Nat.cast_zero,add_zero,mem_Icc] at hl
    change _ ≤ _ ∧ _ ≤ _ at hu
    nlinarith only [hl.1,hu.2,hg]
  have hLc : (L : ℝ)*c ≤ 81920*Real.pi := by
    calc
      _ ≤ (5*α*N/2)*c := mul_le_mul_of_nonneg_right hL hc
      _ = _ := by dsimp [c]; field_simp; ring
  have hstep (i : ℕ) (hi : i ∈ Finset.range L) :
      ‖(𝐞 (sargosQuarticLegendreRemainder N α γ (a+(i+1))) : ℂ)-
        (𝐞 (sargosQuarticLegendreRemainder N α γ (a+i)) : ℂ)‖ ≤
          c+(if i = 0 then 2 else 0)+(if i = L-1 then 2 else 0) := by
    have hn := Finset.mem_range.mp hi
    have hb :
        ‖(𝐞 (sargosQuarticLegendreRemainder N α γ (a+(i+1))) : ℂ)-
          (𝐞 (sargosQuarticLegendreRemainder N α γ (a+i)) : ℂ)‖ ≤ 2 := by
      simpa only [Circle.norm_coe,show (1+1:ℝ) = 2 by norm_num] using
        norm_sub_le (𝐞 (sargosQuarticLegendreRemainder N α γ (a+(i+1))) : ℂ)
          (𝐞 (sargosQuarticLegendreRemainder N α γ (a+i)) : ℂ)
    by_cases hzero : i = 0
    · simp only [if_pos hzero]
      split_ifs <;> linarith
    by_cases hlast : i = L-1
    · simp only [if_neg hzero,if_pos hlast]
      linarith
    have hint (j : ℕ) (hj₀ : 0 < j) (hjL : j < L) :
        a+j ∈ sargosQuarticSlopeRange N α γ := by
      rw [sargosQuarticSlopeRange_eq_endpoint_Ioo hNp hαp hγs]
      have hleft := hr 0 (Nat.zero_le L)
      have hright := hr L le_rfl
      have hjr : (0:ℝ) < j := by exact_mod_cast hj₀
      have hjrL : (j : ℝ) < L := by exact_mod_cast hjL
      simp only [Nat.cast_zero,add_zero,mem_Icc] at hleft
      constructor <;> linarith [hleft.1,hright.2]
    have hh := sargosQuarticLegendreRemainder_character_lipschitz hN hα hγ
      (hint i (by omega) hn) (hint (i+1) (by omega) (by omega))
    have he : a+((i+1 : ℕ) : ℝ)-(a+(i : ℝ)) = 1 := by push_cast; ring
    simp only [he,abs_one,mul_one] at hh
    simp only [if_neg hzero,if_neg hlast,add_zero]
    simpa only [Nat.cast_add,Nat.cast_one,c] using hh
  refine ⟨by positivity,?_,?_⟩
  · intro i hi
    rw [Circle.norm_coe]
    linarith [Real.pi_pos]
  · have hs := Finset.sum_le_sum hstep
    have he₀ : (∑ i ∈ Finset.range L, if i = 0 then (2:ℝ) else 0) ≤ 2 := by
      simp only [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    have he₁ : (∑ i ∈ Finset.range L, if i = L-1 then (2:ℝ) else 0) ≤ 2 := by
      simp only [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_range] at hs
    simpa only [Nat.cast_add,Nat.cast_one] using
      (show (∑ i ∈ Finset.range L,
        ‖(𝐞 (sargosQuarticLegendreRemainder N α γ (a+(i+1))) : ℂ)-
          (𝐞 (sargosQuarticLegendreRemainder N α γ (a+i)) : ℂ)‖) ≤
            5+81920*Real.pi by linarith only [hs,he₀,he₁,hLc])

end TaoTrudgianYang2025
