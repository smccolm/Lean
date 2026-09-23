import TaoTrudgianYang2025.SargosQuarticAmplitudeAbel
import TaoTrudgianYang2025.SargosSlowCharacter

/-! Uniform variation of the literal Legendre residual on its actual open slope range. -/

noncomputable section

open Set
open scoped BigOperators FourierTransform

namespace TaoTrudgianYang2025


theorem sargosQuarticLegendreRemainder_character_lipschitz {N α γ x y : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (hx : x ∈ sargosQuarticSlopeRange N α γ) (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    ‖(𝐞 (sargosQuarticLegendreRemainder N α γ y) : ℂ)-
      (𝐞 (sargosQuarticLegendreRemainder N α γ x) : ℂ)‖ ≤
        (32768*Real.pi/(α*N))*|y-x| := by
  rw [← sargos_ford_character_eq_fourier,← sargos_ford_character_eq_fourier]
  have hh := sargos_character_sub_norm_le
    (sargosQuarticLegendreRemainder N α γ x) (sargosQuarticLegendreRemainder N α γ y)
  have hv := sargosQuarticLegendreRemainder_source_lipschitz hN hα hγ hx hy
  apply (hh.trans (mul_le_mul_of_nonneg_left hv (by positivity))).trans_eq
  ring

theorem finiteVariationBound_sargosQuarticLegendreRemainder
    {N α γ : ℝ} (hN : 9216 ≤ N) (hα : 1/Real.sqrt N ≤ α) (hγ : |γ| ≤ 1/N^3)
    (a : ℝ) (L : ℕ)
    (hr : ∀ i : ℕ, i ≤ L → a+i ∈ sargosQuarticSlopeRange N α γ) :
    FiniteVariationBound (fun i => (𝐞 (sargosQuarticLegendreRemainder N α γ (a+i)) : ℂ))
      L (1+81920*Real.pi) := by
  have hNp : 0 < N := by linarith
  have hαp := (sargosQuartic_source_scale hN hα).1
  have hγs := sargosQuartic_source_smallness hN hα hγ
  have hL : (L : ℝ) ≤ 5*α*N/2 := by
    have hl := hr 0 (Nat.zero_le L)
    have hu := hr L le_rfl
    rw [sargosQuarticSlopeRange_eq_endpoint_Ioo hNp hαp hγs] at hl hu
    have hg := sargosQuarticSlope_gap_upper hNp hαp hγs
      (show N ∈ Icc N (2*N) by constructor <;> linarith)
      (show 2*N ∈ Icc N (2*N) by constructor <;> linarith) (by linarith)
    simp only [Nat.cast_zero,add_zero,mem_Ioo] at hl
    change _ < _ ∧ _ < _ at hu
    nlinarith only [hl.1,hu.2,hg]
  refine ⟨by positivity,?_,?_⟩
  · intro i hi
    rw [Circle.norm_coe]
    linarith [Real.pi_pos]
  · calc
      _ ≤ ∑ _i ∈ Finset.range L, 32768*Real.pi/(α*N) := by
        apply Finset.sum_le_sum
        intro i hi
        have hn := Finset.mem_range.mp hi
        have hh := sargosQuarticLegendreRemainder_character_lipschitz hN hα hγ
          (hr i hn.le) (hr (i+1) hn)
        have he : a+((i+1 : ℕ) : ℝ)-(a+(i : ℝ)) = 1 := by push_cast; ring
        simpa only [he,abs_one,mul_one] using hh
      _ = (L : ℝ)*(32768*Real.pi/(α*N)) := by rw [Finset.sum_const,nsmul_eq_mul,Finset.card_range]
      _ ≤ (5*α*N/2)*(32768*Real.pi/(α*N)) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
      _ = 81920*Real.pi := by field_simp; ring
      _ ≤ 1+81920*Real.pi := by linarith

end TaoTrudgianYang2025
