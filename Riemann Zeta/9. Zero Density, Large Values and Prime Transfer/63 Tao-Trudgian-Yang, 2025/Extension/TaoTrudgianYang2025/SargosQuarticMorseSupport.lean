import TaoTrudgianYang2025.SargosQuarticMorseAmplitude

/-! Smooth compact zero-extension of the actual quartic transported cutoff. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def sargosQuarticMorseWeight (χ : ℝ → ℝ) (ε r : ℝ) : ℝ → ℝ :=
  (sargosQuarticMorseRange ε r).indicator (sargosQuarticMorseAmplitude χ ε r)

theorem sargosQuarticMorseWeight_eq {χ : ℝ → ℝ} {ε r z : ℝ}
    (hz : z ∈ sargosQuarticMorseRange ε r) :
    sargosQuarticMorseWeight χ ε r z = sargosQuarticMorseAmplitude χ ε r z :=
  Set.indicator_of_mem hz _

theorem sargosQuarticMorseWeight_zero_of_not_mem {χ : ℝ → ℝ} {ε r z : ℝ}
    (hz : z ∉ sargosQuarticMorseRange ε r) :
    sargosQuarticMorseWeight χ ε r z = 0 :=
  Set.indicator_of_notMem hz _

theorem sargosQuarticMorseWeight_support_subset {χ : ℝ → ℝ} {ε r : ℝ} :
    Function.support (sargosQuarticMorseWeight χ ε r) ⊆
      sargosQuarticMorseCoordinate ε r '' tsupport χ := by
  intro z hz
  have hr : z ∈ sargosQuarticMorseRange ε r := by
    by_contra hn
    exact hz (sargosQuarticMorseWeight_zero_of_not_mem hn)
  refine ⟨sargosQuarticMorseInverse ε r z,?_,sargosQuarticMorseCoordinate_inverse hr⟩
  apply subset_tsupport χ
  intro hc
  apply hz
  rw [sargosQuarticMorseWeight_eq hr,sargosQuarticMorseAmplitude,hc,zero_mul]

theorem sargosQuarticMorseCoordinate_image_tsupport_isCompact {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    IsCompact (sargosQuarticMorseCoordinate ε r '' tsupport χ) := by
  have hc : IsCompact (tsupport χ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) (hs.trans Ioo_subset_Icc_self)
  apply hc.image_of_continuousOn
  intro u hu
  have hb := (sargosQuarticMorseCoefficient_bounds hε hr
    ⟨(hs hu).1.le,(hs hu).2.le⟩).1
  exact (sargosQuarticMorseCoordinate_contDiffAt (by linarith)).continuousAt.continuousWithinAt

theorem sargosQuarticMorseWeight_tsupport_subset {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    tsupport (sargosQuarticMorseWeight χ ε r) ⊆
      sargosQuarticMorseCoordinate ε r '' tsupport χ :=
  closure_minimal sargosQuarticMorseWeight_support_subset
    (sargosQuarticMorseCoordinate_image_tsupport_isCompact hs hε hr).isClosed

theorem sargosQuarticMorseWeight_tsupport_subset_range {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    tsupport (sargosQuarticMorseWeight χ ε r) ⊆ sargosQuarticMorseRange ε r :=
  (sargosQuarticMorseWeight_tsupport_subset hs hε hr).trans (image_mono hs)

theorem sargosQuarticMorseWeight_contDiff {χ : ℝ → ℝ} {ε r : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    ContDiff ℝ ∞ (sargosQuarticMorseWeight χ ε r) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ sargosQuarticMorseRange ε r
  · apply (sargosQuarticMorseAmplitude_contDiffAt hχ hε hr hz).congr_of_eventuallyEq
    filter_upwards [(sargosQuarticMorseRange_isOpen hε hr).mem_nhds hz] with u hu
    exact sargosQuarticMorseWeight_eq hu
  · have hn : z ∉ tsupport (sargosQuarticMorseWeight χ ε r) :=
      fun h => hz (sargosQuarticMorseWeight_tsupport_subset_range hs hε hr h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem sargosQuarticMorseWeight_hasCompactSupport {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    HasCompactSupport (sargosQuarticMorseWeight χ ε r) :=
  (sargosQuarticMorseCoordinate_image_tsupport_isCompact hs hε hr).of_isClosed_subset
    (isClosed_tsupport _) (sargosQuarticMorseWeight_tsupport_subset hs hε hr)

theorem sargosQuarticMorseWeight_zero {χ : ℝ → ℝ} {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Ioo 0 3) :
    sargosQuarticMorseWeight χ ε r 0 = χ r*(Real.sqrt (2+12*ε*r^2))⁻¹ := by
  rw [sargosQuarticMorseWeight_eq (sargosQuarticMorseRange_zero hr),
    sargosQuarticMorseAmplitude_zero hε hr]

theorem sargosQuarticMorseWeight_tsupport_uniform {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    tsupport (sargosQuarticMorseWeight χ ε r) ⊆ Icc (-6 : ℝ) 6 := by
  intro z hz
  rcases sargosQuarticMorseWeight_tsupport_subset hs hε hr hz with ⟨u,hu,rfl⟩
  have huc : u ∈ Icc 0 3 := ⟨(hs hu).1.le,(hs hu).2.le⟩
  have hd : |u-r| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [huc.1,huc.2,hr.1,hr.2]
  have hb := (sargosQuarticMorseCoordinate_sqrt_bounds hε hr huc).2
  have ha : |sargosQuarticMorseCoordinate ε r u| ≤ 6 := by
    rw [sargosQuarticMorseCoordinate,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [mul_le_mul hd hb (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)]
  exact abs_le.mp ha

end TaoTrudgianYang2025

