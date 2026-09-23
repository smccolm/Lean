import TaoTrudgianYang2025.SargosQuarticExteriorSum

/-! The complete finite quartic Fourier window, with exact integer exterior blocks. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticBufferedWindow_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → l+4*η < b →
      ∀ (N α γ : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      ∀ (a b' : ℤ),
        a ≤ sargosQuarticSupportLower N α γ l η →
        sargosQuarticSupportUpper N α γ b η ≤ b' →
      let L := sargosQuarticSupportLower N α γ l η
      let U := sargosQuarticSupportUpper N α γ b η
      let A := sargosQuarticPlateauLower N α γ l η
      let B := sargosQuarticPlateauUpper N α γ b η
      ‖(∑ y ∈ Finset.Icc a b', sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y)-
        (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        C*(1+Real.log ((B-A-1).toNat : ℝ))+(5*α*N*η+6)*D/Real.sqrt α+
          (4/Real.pi)*(2+Real.log ((L-a).toNat : ℝ)+Real.log ((b'-U).toNat : ℝ)) := by
  obtain ⟨C,hC,D,hD,hcore⟩ := sargosQuarticBufferedSupportCore_error
  refine ⟨C,hC,D,hD,?_⟩
  intro l b η hl hb hη hflat N α γ hN hα hγ a b' ha hb' L U A B
  have he := sargosQuarticBand_endpoints hN hα hγ hη hl hb hflat
  have hLU : L ≤ U := he.1.trans he.2.1
  let f : ℤ → ℂ := fun y => sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y
  let main := ∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y
  have hsplit := sum_int_interval_three_parts f ha hLU hb'
  have heq : (∑ y ∈ Finset.Icc a b', f y)-main =
      ((∑ y ∈ Finset.Icc L U, f y)-main)+
        ((∑ y ∈ Finset.Ico a L, f y)+(∑ y ∈ Finset.Ioc U b', f y)) := by
    rw [hsplit]
    abel
  have hext : ‖(∑ y ∈ Finset.Ico a L, f y)+(∑ y ∈ Finset.Ioc U b', f y)‖ ≤
      (4/Real.pi)*(2+Real.log ((L-a).toNat : ℝ)+Real.log ((b'-U).toNat : ℝ)) := by
    rw [sum_int_Ico_eq_reverse_range f ha,sum_int_Ioc_eq_forward_range f hb']
    simpa only [f,L,U,Int.cast_sub,Int.cast_add,Int.cast_natCast] using
      sargosQuarticExterior_blocks_log hN hα hγ hη hl hb
        (by linarith : l+2*η ≤ b) (L-a).toNat (b'-U).toNat
  have hc := hcore l b η hl hb hη hflat N α γ hN hα hγ
  change ‖(∑ y ∈ Finset.Icc a b', f y)-main‖ ≤ _
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hc hext)

end TaoTrudgianYang2025

