import GafniTao.FordZeroDetectorFinite

/-!
# Ford's detector on independently selected physical heights

The source contour is translated about `1 + it`, whereas the available
Landau good-height theorem selects physical ordinates.  This file therefore
uses independent lower and upper physical heights.  No symmetry about `t` is
assumed.
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordDetectorPhysicalLower (eta yLower : ℝ) : ℂ :=
  ((1 - eta : ℝ) : ℂ) + (yLower : ℂ) * I

noncomputable def fordDetectorPhysicalUpper (eta yUpper : ℝ) : ℂ :=
  ((1 + eta : ℝ) : ℂ) + (yUpper : ℂ) * I

noncomputable def fordDetectorPhysicalZeros
    (eta yLower yUpper : ℝ) : Finset ℂ :=
  (zeroSet 0 (max |yLower| |yUpper|)).filter fun rho =>
    |rho.re - 1| ≤ eta ∧ yLower ≤ rho.im ∧ rho.im ≤ yUpper

noncomputable def fordDetectorPhysicalSingularities
    (eta t yLower yUpper : ℝ) : Finset ℂ :=
  insert (fordDetectorCenter t)
    (insert 1 (fordDetectorPhysicalZeros eta yLower yUpper))

theorem mem_fordDetectorPhysicalRectangle_iff
    {eta yLower yUpper : ℝ} (heta : 0 ≤ eta)
    (hy : yLower ≤ yUpper) {z : ℂ} :
    z ∈ Rectangle (fordDetectorPhysicalLower eta yLower)
        (fordDetectorPhysicalUpper eta yUpper) ↔
      |z.re - 1| ≤ eta ∧ yLower ≤ z.im ∧ z.im ≤ yUpper := by
  rw [Rectangle, mem_reProdIm]
  simp only [fordDetectorPhysicalLower, fordDetectorPhysicalUpper,
    add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_im, mul_im, mul_one, zero_add]
  simp only [add_zero]
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hy]
  simp only [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, hli, hui⟩
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, hli, hui⟩

theorem mem_fordDetectorPhysicalZeros_iff
    {eta yLower yUpper : ℝ} {rho : ℂ} :
    rho ∈ fordDetectorPhysicalZeros eta yLower yUpper ↔
      rho ∈ zeroSet 0 (max |yLower| |yUpper|) ∧
        |rho.re - 1| ≤ eta ∧ yLower ≤ rho.im ∧ rho.im ≤ yUpper := by
  simp [fordDetectorPhysicalZeros]

theorem mem_fordDetectorPhysicalZeros_of_rectangle
    {eta yLower yUpper : ℝ} (heta : 0 ≤ eta) (hetaUpper : eta ≤ 1)
    (hy : yLower ≤ yUpper) {rho : ℂ}
    (hrhoRect : rho ∈ Rectangle (fordDetectorPhysicalLower eta yLower)
      (fordDetectorPhysicalUpper eta yUpper))
    (hrhoZero : riemannZeta rho = 0) :
    rho ∈ fordDetectorPhysicalZeros eta yLower yUpper := by
  have hgeom := (mem_fordDetectorPhysicalRectangle_iff heta hy).mp hrhoRect
  have hleft : -1 ≤ rho.re := by
    have := (abs_le.mp hgeom.1).1
    linarith
  have hstrip := zeta_zero_re_mem_of_neg_one_le hleft hrhoZero
  have himAbs : |rho.im| ≤ max |yLower| |yUpper| := by
    apply abs_le.mpr
    constructor
    · have hneg : -max |yLower| |yUpper| ≤ yLower := by
        calc
          -max |yLower| |yUpper| ≤ -|yLower| := neg_le_neg (le_max_left _ _)
          _ ≤ yLower := neg_abs_le _
      exact hneg.trans hgeom.2.1
    · exact hgeom.2.2.trans (le_abs_self yUpper) |>.trans (le_max_right _ _)
  have hzeroSet : rho ∈ zeroSet 0 (max |yLower| |yUpper|) := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (-max |yLower| |yUpper|) (max |yLower| |yUpper|)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
      0 1 (-max |yLower| |yUpper|) (max |yLower| |yUpper|) rho).mpr ?_,
      hrhoZero⟩
    exact ⟨hstrip.1, hstrip.2, (abs_le.mp himAbs).1,
      (abs_le.mp himAbs).2⟩
  exact (mem_fordDetectorPhysicalZeros_iff).mpr ⟨hzeroSet, hgeom⟩

theorem mem_fordDetectorPhysicalZeros_data
    {eta yLower yUpper : ℝ} {rho : ℂ}
    (hrho : rho ∈ fordDetectorPhysicalZeros eta yLower yUpper) :
    riemannZeta rho = 0 ∧ |rho.re - 1| ≤ eta ∧
      yLower ≤ rho.im ∧ rho.im ≤ yUpper := by
  have h := mem_fordDetectorPhysicalZeros_iff.mp hrho
  exact ⟨(mem_zeroSet_zero_data h.1).2.2.2.2, h.2⟩

theorem differentiableAt_fordCotKernel_translate_at_physicalDetectorZero
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) {rho : ℂ}
    (hrho : rho ∈ fordDetectorPhysicalZeros eta yLower yUpper) :
    DifferentiableAt ℂ
      (fun w : ℂ => fordCotKernel eta (w - fordDetectorCenter t)) rho := by
  have hd := mem_fordDetectorPhysicalZeros_data hrho
  have hcenter : rho ≠ fordDetectorCenter t := by
    intro h
    subst rho
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simp [fordDetectorCenter])) hd.1
  have hre : |(rho - fordDetectorCenter t).re| ≤ eta := by
    simpa [fordDetectorCenter] using hd.2.1
  exact differentiableAt_fordCotKernel_translate_of_abs_re_le
    heta hre hcenter

theorem fordDetectorPhysicalSingularities_mem_nhds
    {eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hyLower : yLower < 0) (hyUpper : 0 < yUpper)
    (hytLower : yLower < t)
    (hytUpper : t < yUpper)
    (hboundary : ∀ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      |rho.re - 1| < eta ∧ yLower < rho.im ∧ rho.im < yUpper) :
    ∀ p ∈ fordDetectorPhysicalSingularities eta t yLower yUpper,
      Rectangle (fordDetectorPhysicalLower eta yLower)
        (fordDetectorPhysicalUpper eta yUpper) ∈ 𝓝 p := by
  have hy : yLower < yUpper := hytLower.trans hytUpper
  intro p hp
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [fordDetectorPhysicalLower, fordDetectorPhysicalUpper,
    add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_im, mul_im, mul_one, zero_add]
  simp only [add_zero]
  rw [Set.uIoo_of_le (by linarith), Set.uIoo_of_le hy.le]
  simp only [Set.mem_Ioo]
  simp only [fordDetectorPhysicalSingularities, Finset.mem_insert] at hp
  rcases hp with rfl | rfl | hp
  · simp [fordDetectorCenter, heta, hytLower, hytUpper]
  · simp [heta, hyLower, hyUpper]
  · have h := hboundary p hp
    exact ⟨⟨by linarith [(abs_lt.mp h.1).1],
      by linarith [(abs_lt.mp h.1).2]⟩, h.2⟩

theorem fordZetaDetectorIntegrand_holomorphicOn_physicalRectangle_diff
    {eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hetaUpper : eta ≤ 1) (hy : yLower ≤ yUpper) :
    HolomorphicOn (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
      (Rectangle (fordDetectorPhysicalLower eta yLower)
          (fordDetectorPhysicalUpper eta yUpper) \
        (fordDetectorPhysicalSingularities eta t yLower yUpper : Set ℂ)) := by
  intro w hw
  have hwCenter : w ≠ fordDetectorCenter t := by
    intro h
    apply hw.2
    simp [h, fordDetectorPhysicalSingularities]
  have hwOne : w ≠ 1 := by
    intro h
    apply hw.2
    simp [h, fordDetectorPhysicalSingularities]
  have hgeom := (mem_fordDetectorPhysicalRectangle_iff heta.le hy).mp hw.1
  have hweight : DifferentiableAt ℂ
      (fun z : ℂ => fordCotKernel eta (z - fordDetectorCenter t)) w := by
    have hre : |(w - fordDetectorCenter t).re| ≤ eta := by
      simpa [fordDetectorCenter] using hgeom.1
    exact differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hwCenter
  have hsur : sharpZetaSurrogate w ≠ 0 := by
    intro hzero
    have hzeta : riemannZeta w = 0 :=
      (sharpZetaSurrogate_eq_zero_iff hwOne).mp hzero
    have hmem : w ∈ fordDetectorPhysicalZeros eta yLower yUpper :=
      mem_fordDetectorPhysicalZeros_of_rectangle heta.le hetaUpper hy hw.1 hzeta
    apply hw.2
    simp [fordDetectorPhysicalSingularities, hmem]
  have hL : DifferentiableAt ℂ fordDetectorZetaLogDeriv w := by
    unfold fordDetectorZetaLogDeriv
    exact (differentiableAt_logDeriv_sharpZetaSurrogate hsur).sub
      ((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub_const (1 : ℂ))
        (sub_ne_zero.mpr hwOne))
  exact (hweight.mul hL).differentiableWithinAt

theorem fordZetaDetectorIntegrand_ne_physical_singularity
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) (ht : 0 < t)
    {p : ℂ} (hp : p ∈
      fordDetectorPhysicalSingularities eta t yLower yUpper) :
    ((fordZetaDetectorIntegrand eta (fordDetectorCenter t)) - fun s =>
        fordDetectorResidueCoefficient eta t p / (s - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hcenterOne : fordDetectorCenter t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordDetectorCenter] at him
    linarith
  simp only [fordDetectorPhysicalSingularities, Finset.mem_insert] at hp
  rcases hp with hcenter | hone | hp
  · subst p
    have hzeta : riemannZeta (fordDetectorCenter t) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp [fordDetectorCenter])
    simpa [fordDetectorResidueCoefficient] using
      fordZetaDetectorIntegrand_near_center heta hcenterOne hzeta
  · subst p
    have hre : |((1 : ℂ) - fordDetectorCenter t).re| ≤ eta := by
      simp [fordDetectorCenter, heta.le]
    have hweight := differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hcenterOne.symm
    simpa [fordDetectorResidueCoefficient, hcenterOne.symm] using
      fordZetaDetectorIntegrand_near_one hweight
  · have hd := mem_fordDetectorPhysicalZeros_data hp
    have hpCenter : p ≠ fordDetectorCenter t := by
      intro h
      subst p
      exact (riemannZeta_ne_zero_of_one_le_re
        (by simp [fordDetectorCenter])) hd.1
    have hpOne : p ≠ 1 := by
      intro h
      subst p
      exact riemannZeta_one_ne_zero hd.1
    have hweight :=
      differentiableAt_fordCotKernel_translate_at_physicalDetectorZero
        (t := t) heta hp
    simpa [fordDetectorResidueCoefficient, hpCenter, hpOne] using
      fordZetaDetectorIntegrand_near_zero hd.1 hweight

theorem fordZetaDetector_physicalRectangleIntegral_eq_residue_sum
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hyLower : yLower < 0)
    (hytLower : yLower < t) (hytUpper : t < yUpper)
    (hboundary : ∀ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      |rho.re - 1| < eta ∧ yLower < rho.im ∧ rho.im < yUpper) :
    RectangleIntegral'
        (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (fordDetectorPhysicalLower eta yLower)
        (fordDetectorPhysicalUpper eta yUpper) =
      ∑ p ∈ fordDetectorPhysicalSingularities eta t yLower yUpper,
        fordDetectorResidueCoefficient eta t p := by
  have hy : yLower < yUpper := hytLower.trans hytUpper
  apply residueTheorem_finset
      (S := fordDetectorPhysicalSingularities eta t yLower yUpper)
      (A := fordDetectorResidueCoefficient eta t)
  · simp [fordDetectorPhysicalLower, fordDetectorPhysicalUpper]
    linarith
  · simp [fordDetectorPhysicalLower, fordDetectorPhysicalUpper]
    linarith
  · exact fordDetectorPhysicalSingularities_mem_nhds
      heta hyLower (ht.trans hytUpper) hytLower hytUpper hboundary
  · exact fordZetaDetectorIntegrand_holomorphicOn_physicalRectangle_diff
      heta hetaUpper hy.le
  · intro p hp
    exact fordZetaDetectorIntegrand_ne_physical_singularity heta ht hp

theorem sum_fordDetectorPhysicalResidueCoefficient
    {eta t yLower yUpper : ℝ} (ht : 0 < t) :
    (∑ p ∈ fordDetectorPhysicalSingularities eta t yLower yUpper,
        fordDetectorResidueCoefficient eta t p) =
      fordDetectorZetaLogDeriv (fordDetectorCenter t) -
        fordCotKernel eta (1 - fordDetectorCenter t) +
        ∑ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta (rho - fordDetectorCenter t) := by
  classical
  have hcenterOne : fordDetectorCenter t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordDetectorCenter] at him
    linarith
  have honeZero : (1 : ℂ) ∉
      fordDetectorPhysicalZeros eta yLower yUpper := by
    intro h
    exact riemannZeta_one_ne_zero (mem_fordDetectorPhysicalZeros_data h).1
  have hcenterZero : fordDetectorCenter t ∉
      fordDetectorPhysicalZeros eta yLower yUpper := by
    intro h
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simp [fordDetectorCenter]))
        (mem_fordDetectorPhysicalZeros_data h).1
  rw [fordDetectorPhysicalSingularities, Finset.sum_insert]
  · rw [Finset.sum_insert honeZero]
    simp only [fordDetectorResidueCoefficient, if_pos]
    have hsum :
        (∑ p ∈ fordDetectorPhysicalZeros eta yLower yUpper,
          if p = fordDetectorCenter t then
            fordDetectorZetaLogDeriv (fordDetectorCenter t)
          else if p = 1 then -fordCotKernel eta (1 - fordDetectorCenter t)
          else (analyticVanishingOrder riemannZeta p : ℂ) *
            fordCotKernel eta (p - fordDetectorCenter t)) =
          ∑ p ∈ fordDetectorPhysicalZeros eta yLower yUpper,
            (analyticVanishingOrder riemannZeta p : ℂ) *
              fordCotKernel eta (p - fordDetectorCenter t) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpCenter : p ≠ fordDetectorCenter t := fun h =>
        hcenterZero (h ▸ hp)
      have hpOne : p ≠ 1 := fun h => honeZero (h ▸ hp)
      simp [hpCenter, hpOne]
    rw [hsum]
    rw [if_neg hcenterOne.symm]
    ring
  · simp [hcenterOne, hcenterZero]

theorem fordZetaDetector_physicalRectangleIntegral_eq_explicit_sum
    {eta t yLower yUpper : ℝ} (heta : 0 < eta) (hetaUpper : eta ≤ 1)
    (ht : 0 < t) (hyLower : yLower < 0)
    (hytLower : yLower < t) (hytUpper : t < yUpper)
    (hboundary : ∀ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      |rho.re - 1| < eta ∧ yLower < rho.im ∧ rho.im < yUpper) :
    RectangleIntegral'
        (fordZetaDetectorIntegrand eta (fordDetectorCenter t))
        (fordDetectorPhysicalLower eta yLower)
        (fordDetectorPhysicalUpper eta yUpper) =
      fordDetectorZetaLogDeriv (fordDetectorCenter t) -
        fordCotKernel eta (1 - fordDetectorCenter t) +
        ∑ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta (rho - fordDetectorCenter t) := by
  rw [fordZetaDetector_physicalRectangleIntegral_eq_residue_sum
    heta hetaUpper ht hyLower hytLower hytUpper hboundary,
    sum_fordDetectorPhysicalResidueCoefficient ht]

end

end GafniTao
