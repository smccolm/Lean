import TaoTrudgianYang2025.SargosQuarticWindowTails

/-! Sharp interior stationary error for the actual positive-curvature quartic mode.
The constant is chosen before all physical parameters and cutoff widths. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticInteriorStationaryConstant : ℝ :=
  128/(7*Real.pi)+sargosQuarticLocalRemainderConstant

theorem sargosQuarticInteriorStationaryConstant_nonneg :
    0 ≤ sargosQuarticInteriorStationaryConstant := by
  unfold sargosQuarticInteriorStationaryConstant
  positivity [sargosQuarticLocalRemainderConstant_nonneg]

theorem sargosQuarticBufferedMode_interior_window {ε r l b η d H T : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ r) (hright : r+d ≤ b-2*η)
    (hH : 0 < H) (hH₁ : H ≤ 1) (hsmall : H < d/2) (hT : 0 < T) :
    ‖sargosQuarticCenteredMode (modelPhaseBufferedCutoff l b η) ε r T-
      (𝐞 (T*sargosQuarticCenteredPhase ε r r) : ℂ)*
        (((deriv (sargosQuarticMorseInverse ε r) 0 : ℝ) : ℂ)*
          ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)))‖ ≤
      sargosQuarticInteriorStationaryConstant/(T*H) := by
  have hgeom (z : ℝ) (hz : z ∈ Icc (-H) H) :=
    sargosQuarticMorseWindow_mem_and_inverse hε hr hd
      (show 0 < r-d by linarith) (show r+d < 3 by linarith) hsmall hz
  have hs : Icc (-H) H ⊆ sargosQuarticMorseRange ε r := fun z hz => (hgeom z hz).1
  have hminus : -H ∈ Icc (-H) H := ⟨le_rfl,by linarith⟩
  have hplus : H ∈ Icc (-H) H := ⟨by linarith,le_rfl⟩
  have hm := abs_lt.mp (hgeom (-H) hminus).2
  have hp := abs_lt.mp (hgeom H hplus).2
  have htail := sargosQuarticBufferedMode_sub_window hε hr hT hη hl hb hH
    (hs hminus) (hs hplus) (show l+η ≤ sargosQuarticMorseInverse ε r (-H) by linarith [hm.1])
    (show sargosQuarticMorseInverse ε r H ≤ b-η by linarith [hp.2])
  have hcentral := sargosQuarticBufferedWeight_local_window_remainder_inverse hε hr hη hl hb hd
    hleft hright hH hH₁ hsmall hT
  let mid := ∫ u in sargosQuarticMorseInverse ε r (-H)..sargosQuarticMorseInverse ε r H,
    (modelPhaseBufferedCutoff l b η u : ℂ)*(𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)
  let main := (𝐞 (T*sargosQuarticCenteredPhase ε r r) : ℂ)*
    (((deriv (sargosQuarticMorseInverse ε r) 0 : ℝ) : ℂ)*
      ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)))
  have hmid : ‖mid-main‖ ≤ sargosQuarticLocalRemainderConstant/(T*H) := by
    dsimp only [mid,main]
    rw [sargosQuarticCentered_window_integral (modelPhaseBufferedCutoff_contDiff l b η).continuous
      hε hr hH.le hs T,← mul_sub,norm_mul,Circle.norm_coe,one_mul]
    exact hcentral
  have hn := norm_add_le
    (sargosQuarticCenteredMode (modelPhaseBufferedCutoff l b η) ε r T-mid) (mid-main)
  rw [sub_add_sub_cancel] at hn
  apply (hn.trans (add_le_add htail hmid)).trans_eq
  unfold sargosQuarticInteriorStationaryConstant
  ring

theorem sargosQuarticBufferedRemainder_interior_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η d : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → 0 < d →
      ∀ (ε r T : ℝ), |ε| ≤ 1/96 → r ∈ Icc 0 3 → 0 < T →
      l+2*η+d ≤ r → r+d ≤ b-2*η →
      ‖sargosQuarticMorseRemainder (modelPhaseBufferedCutoff l b η) ε r T‖ ≤ C/(T*d) := by
  refine ⟨max (4*sargosQuarticInteriorStationaryConstant) 1,le_max_right _ _,?_⟩
  intro l b η d hl hb hη hd ε r T hε hr hT hleft hright
  have hd₁ : d ≤ 1 := by linarith
  have hbound := sargosQuarticBufferedMode_interior_window hε hr hη hl hb hd hleft hright
    (show 0 < d/4 by positivity) (show d/4 ≤ 1 by linarith)
    (show d/4 < d/2 by linarith) hT
  have hs₁₂ := modelPhaseBufferedCutoff_tsupport_model hη hl hb
  have hs : tsupport (modelPhaseBufferedCutoff l b η) ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have hh := hs₁₂ hu
    constructor <;> linarith [hh.1,hh.2]
  have hro : r ∈ Ioo (0 : ℝ) 3 := by constructor <;> linarith
  have hzero : sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r 0 =
      deriv (sargosQuarticMorseInverse ε r) 0 := by
    rw [sargosQuarticMorseWeight_eq (sargosQuarticMorseRange_zero hro),
      sargosQuarticMorseAmplitude,sargosQuarticMorseInverse_zero hε hr,
      modelPhaseBufferedCutoff_one hη (by linarith) (by linarith),one_mul]
  have he :
      sargosQuarticCenteredMode (modelPhaseBufferedCutoff l b η) ε r T-
        (𝐞 (T*sargosQuarticCenteredPhase ε r r) : ℂ)*
          (((deriv (sargosQuarticMorseInverse ε r) 0 : ℝ) : ℂ)*
            ((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))) =
      (𝐞 (T*sargosQuarticCenteredPhase ε r r) : ℂ)*
        sargosQuarticMorseRemainder (modelPhaseBufferedCutoff l b η) ε r T := by
    rw [sargosQuarticCenteredMode_eq_morse hs hε hr T]
    unfold sargosQuarticMorseRemainder
    rw [hzero]
    ring
  rw [he,norm_mul,Circle.norm_coe,one_mul] at hbound
  apply hbound.trans
  calc
    sargosQuarticInteriorStationaryConstant/(T*(d/4)) =
        (4*sargosQuarticInteriorStationaryConstant)/(T*d) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) (mul_pos hT hd).le

theorem sargosQuarticBufferedFourierMode_interior_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η d : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → 0 < d →
      ∀ (N α γ y : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      y ∈ sargosQuarticSlopeRange N α γ →
      l+2*η+d ≤ sargosQuarticInverseSlope N α γ y/N →
      sargosQuarticInverseSlope N α γ y/N+d ≤ b-2*η →
      ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y-
        sargosQuarticStationaryMainTerm N α γ y‖ ≤ C/(α*N*d) := by
  obtain ⟨C,hC,hR⟩ := sargosQuarticBufferedRemainder_interior_uniform
  refine ⟨C,hC,?_⟩
  intro l b η d hl hb hη hd N α γ y hN hα hγ hy hleft hright
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hrc : sargosQuarticInverseSlope N α γ y/N ∈ Icc 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have hχ : modelPhaseBufferedCutoff l b η (sargosQuarticInverseSlope N α γ y/N) = 1 :=
    modelPhaseBufferedCutoff_one hη (by linarith) (by linarith)
  have he := sargosQuarticFourierMode_sub_main_norm
    (modelPhaseBufferedCutoff_tsupport_model hη hl hb) hN hα hγ hy
  rw [hχ,Complex.ofReal_one,one_mul] at he
  rw [he]
  have h := hR l b η d hl hb hη hd (γ*N^2/α) (sargosQuarticInverseSlope N α γ y/N) (α*N^2)
    (sargosQuartic_normalized_coefficient_bound hN hα hγ) hrc (by positivity) hleft hright
  apply (mul_le_mul_of_nonneg_left h hN.le).trans_eq
  field_simp

end TaoTrudgianYang2025

