import TaoTrudgianYang2025.SargosQuarticEndpointBands

/-! Norm cost of restoring all stationary integer endpoints to the quartic main term. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticStationary_endpoint_error {N α γ η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hflat : (N+1)/N+4*η < 2) :
    let A := sargosQuarticPlateauLower N α γ ((N+1)/N) η
    let B := sargosQuarticPlateauUpper N α γ 2 η
    ‖(∑ y ∈ sargosQuarticStationaryFrequencies N α γ, sargosQuarticStationaryMainTerm N α γ y)-
      (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        (5*α/2+10*α*N*η+4)/Real.sqrt α := by
  classical
  intro A B
  have hl : 1 ≤ (N+1)/N := (one_le_div hN).mpr (by linarith)
  have hs := sargosQuarticPlateau_subset_stationaryFrequencies hN hα hγ hη hl le_rfl hflat
  let S := sargosQuarticStationaryFrequencies N α γ \ Finset.Ioo A B
  let f : ℤ → ℂ := fun y => sargosQuarticStationaryMainTerm N α γ y
  have he : (∑ y ∈ sargosQuarticStationaryFrequencies N α γ, f y)-
      (∑ y ∈ Finset.Ioo A B, f y) = ∑ y ∈ S, f y := by
    rw [← Finset.sum_sdiff hs (f := f)]
    abel
  change ‖(∑ y ∈ sargosQuarticStationaryFrequencies N α γ, f y)-
    (∑ y ∈ Finset.Ioo A B, f y)‖ ≤ _
  rw [he]
  have hc := sargosQuarticOmittedStationary_card hN hα hγ hη hflat
  calc
    _ ≤ ∑ _y ∈ S, 1/Real.sqrt α :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy =>
        sargosQuarticStationaryMainTerm_norm_bound_closed hN hα hγ
          (mem_sargosQuarticStationaryFrequencies.mp (Finset.mem_sdiff.mp hy).1))
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)

theorem sargosQuarticStationary_endpoint_error_source {N : ℕ} {α γ : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt (N : ℝ) ≤ α)
    (hα₁ : α ≤ 1) (hγ : |γ| ≤ 1/(N : ℝ)^3) :
    let η := sargosQuarticStationaryWidth N α
    let A := sargosQuarticPlateauLower N α γ (((N : ℝ)+1)/N) η
    let B := sargosQuarticPlateauUpper N α γ 2 η
    ‖(∑ y ∈ sargosQuarticStationaryFrequencies N α γ, sargosQuarticStationaryMainTerm N α γ y)-
      (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        17*(1/Real.sqrt α+1) := by
  intro η A B
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hαp := (sargosQuartic_source_scale hNr hα).1
  have hγs := sargosQuartic_source_smallness hNr hα hγ
  have hηs := sargosQuarticStationaryWidth_source hN hα
  have hh := sargosQuarticStationary_endpoint_error hNp hαp hγs hηs.1 hηs.2.2
  apply hh.trans
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hαp
  have hs₁ : Real.sqrt α ≤ 1 := by nlinarith [Real.sq_sqrt hαp.le]
  have he : 10*α*N*η/Real.sqrt α = 10 := by
    rw [show η = 1/((N : ℝ)*Real.sqrt α) from sargosQuarticStationaryWidth_eq hNp hαp]
    field_simp
    nlinarith [Real.sq_sqrt hαp.le]
  have ha : α/Real.sqrt α ≤ 1 := (div_le_iff₀ hs).mpr (by nlinarith [Real.sq_sqrt hαp.le])
  have hi : 0 ≤ 1/Real.sqrt α := by positivity
  calc
    _ = (5/2)*(α/Real.sqrt α)+10+4*(1/Real.sqrt α) := by
      rw [add_div,add_div,he]
      ring
    _ ≤ 17*(1/Real.sqrt α+1) := by nlinarith only [ha,hi]

end TaoTrudgianYang2025

