import TaoTrudgianYang2025.SargosQuarticExteriorModes

/-! Actual quartic slope intervals and conversion from frequency gaps to physical distances. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosQuarticSlope_gap_upper {N α γ a b : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (ha : a ∈ Icc N (2*N)) (hb : b ∈ Icc N (2*N)) (hab : a ≤ b) :
    sargosQuarticSlope α γ b-sargosQuarticSlope α γ a ≤ (5*α/2)*(b-a) := by
  apply (convex_Icc N (2*N)).image_sub_le_mul_sub_of_deriv_le
    (contDiff_sargosQuarticSlope α γ).continuous.continuousOn
    (fun u _ => (sargosQuarticSlope_hasDerivAt α γ u).differentiableAt.differentiableWithinAt)
    _ a ha b hb hab
  intro u hu
  rw [(sargosQuarticSlope_hasDerivAt α γ u).deriv]
  exact (sargosQuarticPhase_curvature hN hα hγ (interior_subset hu)).2

theorem sargosQuarticSlopeRange_eq_endpoint_Ioo {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    sargosQuarticSlopeRange N α γ =
      Ioo (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N)) := by
  have hm := sargosQuarticSlope_strictMonoOn hN hα hγ
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨hm ⟨le_rfl,by linarith⟩ ⟨hu.1.le,hu.2.le⟩ hu.1,
      hm ⟨hu.1.le,hu.2.le⟩ ⟨by linarith,le_rfl⟩ hu.2⟩
  · intro hy
    obtain ⟨u,hu,he⟩ := intermediate_value_Ioo (show N ≤ 2*N by linarith)
      (contDiff_sargosQuarticSlope α γ).continuous.continuousOn hy
    exact ⟨u,hu,he⟩

theorem sargosQuarticInverseSlope_interior_of_gap {N α γ y a b lam : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ)
    (ha : a ∈ Icc N (2*N)) (hb : b ∈ Icc N (2*N)) (hlam : 0 < lam)
    (hleft : sargosQuarticSlope α γ a+lam ≤ y)
    (hright : y+lam ≤ sargosQuarticSlope α γ b) :
    a+lam/(5*α/2) ≤ sargosQuarticInverseSlope N α γ y ∧
      sargosQuarticInverseSlope N α γ y+lam/(5*α/2) ≤ b := by
  have hw := sargosQuarticInverseSlope_mem hN hα hγ hy
  have hwc : sargosQuarticInverseSlope N α γ y ∈ Icc N (2*N) := ⟨hw.1.le,hw.2.le⟩
  have hm := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
  have haw : a < sargosQuarticInverseSlope N α γ y := by
    by_contra h
    have hh := hm hwc ha (le_of_not_gt h)
    rw [sargosQuarticSlope_inverse hy] at hh
    linarith
  have hwb : sargosQuarticInverseSlope N α γ y < b := by
    by_contra h
    have hh := hm hb hwc (le_of_not_gt h)
    rw [sargosQuarticSlope_inverse hy] at hh
    linarith
  have hL := sargosQuarticSlope_gap_upper hN hα hγ ha hwc haw.le
  have hR := sargosQuarticSlope_gap_upper hN hα hγ hwc hb hwb.le
  rw [sargosQuarticSlope_inverse hy] at hL hR
  have hp : 0 < 5*α/2 := by positivity
  have hL' : lam/(5*α/2) ≤ sargosQuarticInverseSlope N α γ y-a :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  have hR' : lam/(5*α/2) ≤ b-sargosQuarticInverseSlope N α γ y :=
    (div_le_iff₀ hp).mpr (by nlinarith)
  constructor <;> linarith

theorem sargosQuarticBufferedFourierMode_interior_frequency_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → l+4*η < b →
      ∀ (N α γ y lam : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) → 0 < lam →
      sargosQuarticSlope α γ (N*(l+2*η))+lam ≤ y →
      y+lam ≤ sargosQuarticSlope α γ (N*(b-2*η)) →
      ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y-
        sargosQuarticStationaryMainTerm N α γ y‖ ≤ C/lam := by
  obtain ⟨C,hC,hmode⟩ := sargosQuarticBufferedFourierMode_interior_uniform
  refine ⟨5*C/2,by linarith,?_⟩
  intro l b η hl hb hη hflat N α γ y lam hN hα hγ hlam hleft hright
  have ha : N*(l+2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hb' : N*(b-2*η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hm := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
  have hy : y ∈ sargosQuarticSlopeRange N α γ := by
    rw [sargosQuarticSlopeRange_eq_endpoint_Ioo hN hα hγ]
    have hL := hm (show N ∈ Icc N (2*N) by constructor <;> linarith) ha ha.1
    have hR := hm hb' (show 2*N ∈ Icc N (2*N) by constructor <;> linarith) hb'.2
    constructor <;> linarith
  have hi := sargosQuarticInverseSlope_interior_of_gap hN hα hγ hy ha hb' hlam hleft hright
  let d := lam/(5*α*N/2)
  have hd : 0 < d := by dsimp [d]; positivity
  have he : d*N = lam/(5*α/2) := by dsimp [d]; field_simp
  have hL : l+2*η+d ≤ sargosQuarticInverseSlope N α γ y/N := by
    apply (le_div_iff₀ hN).mpr
    rw [add_mul,he]
    nlinarith [hi.1]
  have hR : sargosQuarticInverseSlope N α γ y/N+d ≤ b-2*η := by
    have hh : sargosQuarticInverseSlope N α γ y/N ≤ b-2*η-d := by
      apply (div_le_iff₀ hN).mpr
      rw [sub_mul,he]
      nlinarith [hi.2]
    linarith
  have h := hmode l b η d hl hb hη hd N α γ y hN hα hγ hy hL hR
  apply h.trans_eq
  dsimp [d]
  field_simp

end TaoTrudgianYang2025

