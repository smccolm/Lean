import TaoTrudgianYang2025.SargosQuarticMorse

/-! The actual inverse quadratic coordinate on the extended quartic interval. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def sargosQuarticMorseRange (ε r : ℝ) : Set ℝ :=
  sargosQuarticMorseCoordinate ε r '' Ioo 0 3

def sargosQuarticMorseInverse (ε r : ℝ) : ℝ → ℝ :=
  Function.invFunOn (sargosQuarticMorseCoordinate ε r) (Icc 0 3)

theorem sargosQuarticMorseInverse_coordinate {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    sargosQuarticMorseInverse ε r (sargosQuarticMorseCoordinate ε r u) = u :=
  (sargosQuarticMorseCoordinate_strictMonoOn hε hr).injOn.leftInvOn_invFunOn hu

theorem sargosQuarticMorseInverse_mem {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) :
    sargosQuarticMorseInverse ε r z ∈ Ioo 0 3 := by
  rcases hz with ⟨u,hu,rfl⟩
  rw [sargosQuarticMorseInverse_coordinate hε hr ⟨hu.1.le,hu.2.le⟩]
  exact hu

theorem sargosQuarticMorseCoordinate_inverse {ε r z : ℝ}
    (hz : z ∈ sargosQuarticMorseRange ε r) :
    sargosQuarticMorseCoordinate ε r (sargosQuarticMorseInverse ε r z) = z := by
  apply Function.invFunOn_eq
  rcases hz with ⟨u,hu,rfl⟩
  exact ⟨u,⟨hu.1.le,hu.2.le⟩,rfl⟩

theorem sargosQuarticMorseCoordinate_hasStrictDerivAt {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    HasStrictDerivAt (sargosQuarticMorseCoordinate ε r)
      (deriv (sargosQuarticMorseCoordinate ε r) u) u := by
  have hp := (sargosQuarticMorseCoefficient_bounds hε hr hu).1
  exact (sargosQuarticMorseCoordinate_contDiffAt (by linarith)).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)

theorem sargosQuarticMorseInverse_hasStrictDerivAt {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) :
    HasStrictDerivAt (sargosQuarticMorseInverse ε r)
      (deriv (sargosQuarticMorseCoordinate ε r) (sargosQuarticMorseInverse ε r z))⁻¹ z := by
  rcases hz with ⟨u,hu,rfl⟩
  have huc : u ∈ Icc 0 3 := ⟨hu.1.le,hu.2.le⟩
  rw [sargosQuarticMorseInverse_coordinate hε hr huc]
  have hd := sargosQuarticMorseCoordinate_hasStrictDerivAt hε hr huc
  have hp := (sargosQuarticMorseCoordinate_deriv_bounds hε hr huc).1
  apply hd.to_local_left_inverse (by linarith)
  filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
  exact sargosQuarticMorseInverse_coordinate hε hr ⟨hx.1.le,hx.2.le⟩

theorem sargosQuarticMorseRange_isOpen {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    IsOpen (sargosQuarticMorseRange ε r) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨u,hu,rfl⟩
  have huc : u ∈ Icc 0 3 := ⟨hu.1.le,hu.2.le⟩
  have hd := sargosQuarticMorseCoordinate_hasStrictDerivAt hε hr huc
  have hp := (sargosQuarticMorseCoordinate_deriv_bounds hε hr huc).1
  have hi := Filter.image_mem_map (m := sargosQuarticMorseCoordinate ε r) (isOpen_Ioo.mem_nhds hu)
  rwa [hd.map_nhds_eq (by linarith)] at hi

theorem sargosQuarticMorseInverse_contDiffAt {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) :
    ContDiffAt ℝ ∞ (sargosQuarticMorseInverse ε r) z := by
  rcases hz with ⟨u,hu,rfl⟩
  have huc : u ∈ Icc 0 3 := ⟨hu.1.le,hu.2.le⟩
  have hp := (sargosQuarticMorseCoefficient_bounds hε hr huc).1
  have hc := sargosQuarticMorseCoordinate_contDiffAt (by linarith : 0 < sargosQuarticMorseCoefficient ε r u)
  have hd := sargosQuarticMorseCoordinate_hasStrictDerivAt hε hr huc
  have hpos := (sargosQuarticMorseCoordinate_deriv_bounds hε hr huc).1
  have he := hd.hasStrictFDerivAt_equiv (by linarith)
  have hg : ∀ᶠ x in 𝓝 u,
      sargosQuarticMorseInverse ε r (sargosQuarticMorseCoordinate ε r x) = x := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact sargosQuarticMorseInverse_coordinate hε hr ⟨hx.1.le,hx.2.le⟩
  exact (hc.to_localInverse he.hasFDerivAt (by simp)).congr_of_eventuallyEq
    (he.localInverse_unique hg)

theorem sargosQuarticMorseRange_zero {ε r : ℝ} (hr : r ∈ Ioo 0 3) :
    0 ∈ sargosQuarticMorseRange ε r :=
  ⟨r,hr,sargosQuarticMorseCoordinate_at_center ε r⟩

theorem sargosQuarticMorseInverse_zero {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    sargosQuarticMorseInverse ε r 0 = r := by
  have h := sargosQuarticMorseInverse_coordinate hε hr hr
  rwa [sargosQuarticMorseCoordinate_at_center] at h

theorem sargosQuarticMorseInverse_deriv_bounds {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) :
    4/25 ≤ deriv (sargosQuarticMorseInverse ε r) z ∧
      deriv (sargosQuarticMorseInverse ε r) z ≤ 16/7 := by
  have hu := sargosQuarticMorseInverse_mem hε hr hz
  have hb := sargosQuarticMorseCoordinate_deriv_bounds hε hr ⟨hu.1.le,hu.2.le⟩
  have hp : 0 < deriv (sargosQuarticMorseCoordinate ε r) (sargosQuarticMorseInverse ε r z) :=
    lt_of_lt_of_le (by norm_num) hb.1
  rw [(sargosQuarticMorseInverse_hasStrictDerivAt hε hr hz).hasDerivAt.deriv,← one_div]
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [hb.2]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [hb.1]

theorem sargosQuarticMorseCoordinate_deriv_center {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    deriv (sargosQuarticMorseCoordinate ε r) r = Real.sqrt (2+12*ε*r^2) := by
  have hp := (sargosQuarticMorseCoefficient_bounds hε hr hr).1
  have hc : 2*sargosQuarticMorseCoefficient ε r r = 2+12*ε*r^2 := by
    unfold sargosQuarticMorseCoefficient
    ring
  have hn : sargosQuarticMorseNumerator ε r r = 2+12*ε*r^2 := by
    unfold sargosQuarticMorseNumerator
    ring
  have hpos : 0 < 2+12*ε*r^2 := by linarith
  rw [(sargosQuarticMorseCoordinate_hasDerivAt (by linarith)).deriv,hc,hn]
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.2 hpos))).mpr
  nlinarith [Real.sq_sqrt hpos.le]

theorem sargosQuarticMorseInverse_deriv_zero {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Ioo 0 3) :
    deriv (sargosQuarticMorseInverse ε r) 0 = (Real.sqrt (2+12*ε*r^2))⁻¹ := by
  have hrc : r ∈ Icc 0 3 := ⟨hr.1.le,hr.2.le⟩
  rw [(sargosQuarticMorseInverse_hasStrictDerivAt hε hrc (sargosQuarticMorseRange_zero hr)).hasDerivAt.deriv,
    sargosQuarticMorseInverse_zero hε hrc,sargosQuarticMorseCoordinate_deriv_center hε hrc]


end TaoTrudgianYang2025
