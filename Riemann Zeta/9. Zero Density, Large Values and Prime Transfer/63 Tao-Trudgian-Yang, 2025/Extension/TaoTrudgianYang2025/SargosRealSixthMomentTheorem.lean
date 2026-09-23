import TaoTrudgianYang2025.SargosRealQuarticMomentTransfer

/-! The actual real-block maximal sixth moment, with the endpoint error absorbed. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosRealQuartic_maximal_sixth_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℝ, 2 ≤ M → ∀ z : ℤ → ℂ,
      (∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1) →
      ∀ lambda : ℝ, 0 < lambda → ∀ c d : ℝ,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        (sargosRealQuarticMaximum M z α γ)^6) ≤
        C*(lambda*M^(3+ε)+M^ε) := by
  obtain ⟨C,hC,hNat⟩ := sargosQuartic_maximal_sixth_moment ε hε
  refine ⟨32*(C+1),by linarith only [hC],?_⟩
  intro M hM z hz lambda hlambda c d
  have hMp : 0 < M := by linarith only [hM]
  have hM₁ : 1 ≤ M := by linarith only [hM]
  let m := ⌊M⌋₊
  have hm : 2 ≤ m := Nat.le_floor hM
  have hmM : (m:ℝ) ≤ M := Nat.floor_le hMp.le
  have hzNat : ∀ n ∈ sargosSourceInterval m, ‖z n‖ ≤ 1 := by
    intro n hn
    exact hz n (sargosSourceInterval_subset_real hMp.le hn)
  have hn := hNat m hm z hzNat lambda hlambda c d
  have hp₁ := Real.rpow_le_rpow (Nat.cast_nonneg m) hmM
    (by linarith only [hε] : 0 ≤ 3+ε)
  have hp₂ := Real.rpow_le_rpow (Nat.cast_nonneg m) hmM hε.le
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hp₁ hlambda.le) hp₂
  have hmain := hn.trans (mul_le_mul_of_nonneg_left hsum (by linarith only [hC] : 0 ≤ C))
  have herror : lambda ≤ lambda*M^(3+ε)+M^ε := by
    have hp := Real.one_le_rpow hM₁ (by linarith only [hε] : 0 ≤ 3+ε)
    have hh := mul_le_mul_of_nonneg_left hp hlambda.le
    have hq : 0 ≤ M^ε := by positivity
    nlinarith only [hh,hq]
  calc
    _ ≤ 32*((∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        (sargosQuarticPrefixMaximum m z α γ)^6)+lambda) :=
      sargosRealQuartic_sixth_rectangle_le_natural hMp.le z hz hlambda.le c d
    _ ≤ 32*(C*(lambda*M^(3+ε)+M^ε)+(lambda*M^(3+ε)+M^ε)) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain herror) (by norm_num)
    _ = _ := by ring

end TaoTrudgianYang2025
