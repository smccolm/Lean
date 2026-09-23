import TaoTrudgianYang2025.SargosQuarticTransitionBands

/-! Replacing the actual quartic support-frequency block by its interior stationary terms. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticBufferedTransition_error :
    ∃ C : ℝ, 0 < C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → l+4*η < b →
      ∀ (N α γ : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      ‖∑ y ∈ (Finset.Icc (sargosQuarticSupportLower N α γ l η)
          (sargosQuarticSupportUpper N α γ b η)) \
        (Finset.Ioo (sargosQuarticPlateauLower N α γ l η)
          (sargosQuarticPlateauUpper N α γ b η)),
        sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
          (5*α*N*η+6)*C/Real.sqrt α := by
  obtain ⟨C,hC,hmode⟩ := sargosQuarticBufferedFourierMode_uniform_curvature
  refine ⟨C,hC,?_⟩
  intro l b η hl hb hη hflat N α γ hN hα hγ
  have hc := sargosQuarticTransition_card_le hN hα hγ hη hl hb hflat
  calc
    _ ≤ ∑ _y ∈ (Finset.Icc (sargosQuarticSupportLower N α γ l η)
          (sargosQuarticSupportUpper N α γ b η)) \
        (Finset.Ioo (sargosQuarticPlateauLower N α γ l η)
          (sargosQuarticPlateauUpper N α γ b η)), C/Real.sqrt α :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ =>
        hmode l b η hl hb hη N α γ y hN hα hγ)
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)

theorem sargosQuarticBufferedSupportCore_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → l+4*η < b →
      ∀ (N α γ : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      let L := sargosQuarticSupportLower N α γ l η
      let U := sargosQuarticSupportUpper N α γ b η
      let A := sargosQuarticPlateauLower N α γ l η
      let B := sargosQuarticPlateauUpper N α γ b η
      ‖(∑ y ∈ Finset.Icc L U, sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y)-
        (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        C*(1+Real.log ((B-A-1).toNat : ℝ))+(5*α*N*η+6)*D/Real.sqrt α := by
  obtain ⟨C,hC,hinterior⟩ := sargosQuarticBufferedInteriorBlock_error
  obtain ⟨D,hD,htransition⟩ := sargosQuarticBufferedTransition_error
  refine ⟨C,hC,D,hD,?_⟩
  intro l b η hl hb hη hflat N α γ hN hα hγ L U A B
  have he := sargosQuarticBand_endpoints hN hα hγ hη hl hb hflat
  have hLA : L ≤ A := he.1
  have hBU : B ≤ U := he.2.2.2
  have hs : Finset.Ioo A B ⊆ Finset.Icc L U := by
    intro y hy
    simp only [Finset.mem_Ioo,Finset.mem_Icc] at hy ⊢
    omega
  let f : ℤ → ℂ := fun y => sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y
  let main : ℤ → ℂ := fun y => sargosQuarticStationaryMainTerm N α γ y
  have hsplit : (∑ y ∈ Finset.Icc L U, f y)-(∑ y ∈ Finset.Ioo A B, main y) =
      (∑ y ∈ Finset.Ioo A B, (f y-main y))+
        ∑ y ∈ (Finset.Icc L U) \ (Finset.Ioo A B), f y := by
    rw [← Finset.sum_sdiff hs (f := f),Finset.sum_sub_distrib]
    abel
  have hi := hinterior l b η hl hb hη hflat N α γ A B hN hα hγ
    (Int.le_ceil _) (Int.floor_le _)
  have ht := htransition l b η hl hb hη hflat N α γ hN hα hγ
  change ‖(∑ y ∈ Finset.Icc L U, f y)-(∑ y ∈ Finset.Ioo A B, main y)‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hi ht)

end TaoTrudgianYang2025

