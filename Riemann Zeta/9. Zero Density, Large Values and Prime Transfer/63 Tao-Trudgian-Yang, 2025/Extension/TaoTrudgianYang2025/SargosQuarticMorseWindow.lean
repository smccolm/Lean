import TaoTrudgianYang2025.SargosQuarticMorseGeometry

/-! Actual quadratic windows and cutoff-plateau derivatives without width loss. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem sargosQuarticMorseWindow_mem_and_inverse {ε r d H z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hd : 0 < d)
    (hleft : 0 < r-d) (hright : r+d < 3) (hH : H < d/2)
    (hz : z ∈ Icc (-H) H) :
    z ∈ sargosQuarticMorseRange ε r ∧ |sargosQuarticMorseInverse ε r z-r| < d := by
  have ha : r-d ∈ Ioo (0 : ℝ) 3 := ⟨hleft,by linarith [hr.2]⟩
  have hb : r+d ∈ Ioo (0 : ℝ) 3 := ⟨by linarith [hr.1],hright⟩
  have hs : Icc (r-d) (r+d) ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    exact ⟨ha.1.trans_le hu.1,hu.2.trans_lt hb.2⟩
  have hm := sargosQuarticMorseCoordinate_strictMonoOn hε hr
  have hwa : sargosQuarticMorseCoordinate ε r (r-d) < 0 := by
    simpa only [sargosQuarticMorseCoordinate_at_center] using
      hm ⟨ha.1.le,ha.2.le⟩ hr (show r-d < r by linarith)
  have hwb : 0 < sargosQuarticMorseCoordinate ε r (r+d) := by
    simpa only [sargosQuarticMorseCoordinate_at_center] using
      hm hr ⟨hb.1.le,hb.2.le⟩ (show r < r+d by linarith)
  have hba := (sargosQuarticMorseCoordinate_abs_bounds hε hr ⟨ha.1.le,ha.2.le⟩).1
  have hbb := (sargosQuarticMorseCoordinate_abs_bounds hε hr ⟨hb.1.le,hb.2.le⟩).1
  rw [show r-d-r = -d by ring,abs_neg,abs_of_pos hd,abs_of_neg hwa] at hba
  rw [show r+d-r = d by ring,abs_of_pos hd,abs_of_pos hwb] at hbb
  have hc : ContinuousOn (sargosQuarticMorseCoordinate ε r) (Icc (r-d) (r+d)) := by
    intro u hu
    have hp := (sargosQuarticMorseCoefficient_bounds hε hr ⟨(hs hu).1.le,(hs hu).2.le⟩).1
    exact (sargosQuarticMorseCoordinate_contDiffAt (by linarith)).continuousAt.continuousWithinAt
  have hz' : z ∈ sargosQuarticMorseRange ε r := by
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc (show r-d ≤ r+d by linarith) hc
      (show z ∈ Icc (sargosQuarticMorseCoordinate ε r (r-d))
        (sargosQuarticMorseCoordinate ε r (r+d)) by constructor <;> linarith [hz.1,hz.2])
    exact ⟨u,hs hu,he⟩
  refine ⟨hz',?_⟩
  have hu := sargosQuarticMorseInverse_mem hε hr hz'
  have hb' := (sargosQuarticMorseCoordinate_abs_bounds hε hr ⟨hu.1.le,hu.2.le⟩).1
  rw [sargosQuarticMorseCoordinate_inverse hz'] at hb'
  have habs : |z| ≤ H := abs_le.mpr hz
  nlinarith

theorem sargosQuarticBufferedWeight_iteratedDeriv_of_flat {ε r z l b η : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) (hη : 0 < η)
    (hleft : l+2*η < sargosQuarticMorseInverse ε r z)
    (hright : sargosQuarticMorseInverse ε r z < b-2*η) (n : ℕ) :
    iteratedDeriv n (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) z =
      iteratedDeriv (n+1) (sargosQuarticMorseInverse ε r) z := by
  rw [sargosQuarticMorseWeight_iteratedDeriv_eq hε hr hz,iteratedDeriv_succ']
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hi := (sargosQuarticMorseInverse_contDiffAt hε hr hz).continuousAt
  have hn : ∀ᶠ x in 𝓝 z, sargosQuarticMorseInverse ε r x ∈ Ioo (l+2*η) (b-2*η) :=
    hi (isOpen_Ioo.mem_nhds ⟨hleft,hright⟩)
  filter_upwards [hn] with x hx
  simp only [sargosQuarticMorseAmplitude,modelPhaseBufferedCutoff_one hη hx.1.le hx.2.le,one_mul]

theorem sargosQuarticBufferedWeight_local_jet_bound {ε r z l b η d H : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hd : 0 < d)
    (hleft : l+2*η+d ≤ r) (hright : r+d ≤ b-2*η)
    (hH : H < d/2) (hz : z ∈ Icc (-H) H) (n : ℕ) :
    |iteratedDeriv n (sargosQuarticMorseWeight (modelPhaseBufferedCutoff l b η) ε r) z| ≤
      sargosQuarticMorseInverseDerivativeBound (n+1) := by
  obtain ⟨hz',hi⟩ := sargosQuarticMorseWindow_mem_and_inverse hε hr hd
    (by linarith) (by linarith) hH hz
  have hi' := abs_lt.mp hi
  rw [sargosQuarticBufferedWeight_iteratedDeriv_of_flat hε hr hz' hη
    (by linarith [hi'.1]) (by linarith [hi'.2]) n]
  exact sargosQuarticMorseInverse_iteratedDeriv_bound hε hr hz' (n+1)

end TaoTrudgianYang2025

