import GafniTao.FordShiftedZeroDetectorHorizontalBound

/-!
# Shifted Ford detector on independent physical heights
-/

open Complex Filter Set Topology Asymptotics
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def fordShiftedDetectorPhysicalLower
    (sigma eta yLower : ℝ) : ℂ :=
  ((sigma - eta : ℝ) : ℂ) + (yLower : ℂ) * I

noncomputable def fordShiftedDetectorPhysicalUpper
    (sigma eta yUpper : ℝ) : ℂ :=
  ((sigma + eta : ℝ) : ℂ) + (yUpper : ℂ) * I

noncomputable def fordShiftedDetectorPhysicalZeros
    (sigma eta yLower yUpper : ℝ) : Finset ℂ :=
  (zeroSet 0 (max |yLower| |yUpper|)).filter fun rho =>
    |rho.re - sigma| ≤ eta ∧ yLower ≤ rho.im ∧ rho.im ≤ yUpper

noncomputable def fordShiftedDetectorPhysicalSingularities
    (sigma eta t yLower yUpper : ℝ) : Finset ℂ :=
  insert (fordShiftedDetectorCenter sigma t)
    (insert 1
      (fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper))

theorem mem_fordShiftedDetectorPhysicalRectangle_iff
    {sigma eta yLower yUpper : ℝ} (heta : 0 ≤ eta)
    (hy : yLower ≤ yUpper) {z : ℂ} :
    z ∈ Rectangle
        (fordShiftedDetectorPhysicalLower sigma eta yLower)
        (fordShiftedDetectorPhysicalUpper sigma eta yUpper) ↔
      |z.re - sigma| ≤ eta ∧
        yLower ≤ z.im ∧ z.im ≤ yUpper := by
  rw [Rectangle, mem_reProdIm]
  simp only [fordShiftedDetectorPhysicalLower,
    fordShiftedDetectorPhysicalUpper, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, sub_zero, add_im, mul_im,
    mul_one, zero_add, add_zero]
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hy]
  simp only [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, hli, hui⟩
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, hli, hui⟩

theorem mem_fordShiftedDetectorPhysicalZeros_iff
    {sigma eta yLower yUpper : ℝ} {rho : ℂ} :
    rho ∈ fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper ↔
      rho ∈ zeroSet 0 (max |yLower| |yUpper|) ∧
        |rho.re - sigma| ≤ eta ∧
          yLower ≤ rho.im ∧ rho.im ≤ yUpper := by
  simp [fordShiftedDetectorPhysicalZeros]

theorem mem_fordShiftedDetectorPhysicalZeros_of_rectangle
    {sigma eta yLower yUpper : ℝ} (heta : 0 ≤ eta)
    (hy : yLower ≤ yUpper) (hleft : -1 ≤ sigma - eta)
    {rho : ℂ}
    (hrhoRect : rho ∈ Rectangle
      (fordShiftedDetectorPhysicalLower sigma eta yLower)
      (fordShiftedDetectorPhysicalUpper sigma eta yUpper))
    (hrhoZero : riemannZeta rho = 0) :
    rho ∈ fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper := by
  have hgeom :=
    (mem_fordShiftedDetectorPhysicalRectangle_iff heta hy).mp hrhoRect
  have hrhoLeft : -1 ≤ rho.re := by
    have := (abs_le.mp hgeom.1).1
    linarith
  have hstrip := zeta_zero_re_mem_of_neg_one_le hrhoLeft hrhoZero
  have himAbs : |rho.im| ≤ max |yLower| |yUpper| := by
    apply abs_le.mpr
    constructor
    · have hneg : -max |yLower| |yUpper| ≤ yLower := by
        calc
          -max |yLower| |yUpper| ≤ -|yLower| :=
            neg_le_neg (le_max_left _ _)
          _ ≤ yLower := neg_abs_le _
      exact hneg.trans hgeom.2.1
    · exact hgeom.2.2.trans (le_abs_self yUpper) |>.trans
        (le_max_right _ _)
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
  exact (mem_fordShiftedDetectorPhysicalZeros_iff).mpr
    ⟨hzeroSet, hgeom⟩

theorem mem_fordShiftedDetectorPhysicalZeros_data
    {sigma eta yLower yUpper : ℝ} {rho : ℂ}
    (hrho : rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper) :
    riemannZeta rho = 0 ∧ |rho.re - sigma| ≤ eta ∧
      yLower ≤ rho.im ∧ rho.im ≤ yUpper := by
  have h := mem_fordShiftedDetectorPhysicalZeros_iff.mp hrho
  exact ⟨(mem_zeroSet_zero_data h.1).2.2.2.2, h.2⟩

theorem differentiableAt_fordCotKernel_translate_at_shiftedPhysicalZero
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) {rho : ℂ}
    (hrho : rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper) :
    DifferentiableAt ℂ
      (fun w : ℂ => fordCotKernel eta
        (w - fordShiftedDetectorCenter sigma t)) rho := by
  have hd := mem_fordShiftedDetectorPhysicalZeros_data hrho
  have hcenter : rho ≠ fordShiftedDetectorCenter sigma t := by
    intro h
    subst rho
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simpa using hsigma)) hd.1
  have hre :
      |(rho - fordShiftedDetectorCenter sigma t).re| ≤ eta := by
    simpa [fordShiftedDetectorCenter] using hd.2.1
  exact differentiableAt_fordCotKernel_translate_of_abs_re_le
    heta hre hcenter

theorem fordShiftedDetectorPhysicalSingularities_mem_nhds
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (hPole : sigma - 1 < eta)
    (hyLower : yLower < 0) (hyUpper : 0 < yUpper)
    (hytLower : yLower < t) (hytUpper : t < yUpper)
    (hboundary : ∀ rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper,
      |rho.re - sigma| < eta ∧
        yLower < rho.im ∧ rho.im < yUpper) :
    ∀ p ∈ fordShiftedDetectorPhysicalSingularities
        sigma eta t yLower yUpper,
      Rectangle (fordShiftedDetectorPhysicalLower sigma eta yLower)
        (fordShiftedDetectorPhysicalUpper sigma eta yUpper) ∈ 𝓝 p := by
  have hy : yLower < yUpper := hytLower.trans hytUpper
  intro p hp
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [fordShiftedDetectorPhysicalLower,
    fordShiftedDetectorPhysicalUpper, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, sub_zero, add_im, mul_im,
    mul_one, zero_add, add_zero]
  rw [Set.uIoo_of_le (by linarith), Set.uIoo_of_le hy.le]
  simp only [Set.mem_Ioo]
  simp only [fordShiftedDetectorPhysicalSingularities,
    Finset.mem_insert] at hp
  rcases hp with rfl | rfl | hp
  · simp [fordShiftedDetectorCenter, heta, hytLower, hytUpper]
  · constructor
    · norm_num
      constructor <;> linarith
    · exact ⟨hyLower, hyUpper⟩
  · have h := hboundary p hp
    exact ⟨⟨by linarith [(abs_lt.mp h.1).1],
      by linarith [(abs_lt.mp h.1).2]⟩, h.2⟩

theorem fordZetaShiftedDetectorIntegrand_holomorphicOn_physicalRectangle_diff
    {sigma eta t yLower yUpper : ℝ} (heta : 0 < eta)
    (hy : yLower ≤ yUpper) (hleft : -1 ≤ sigma - eta) :
    HolomorphicOn
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (Rectangle (fordShiftedDetectorPhysicalLower sigma eta yLower)
          (fordShiftedDetectorPhysicalUpper sigma eta yUpper) \
        (fordShiftedDetectorPhysicalSingularities
          sigma eta t yLower yUpper : Set ℂ)) := by
  intro w hw
  have hwCenter : w ≠ fordShiftedDetectorCenter sigma t := by
    intro h
    apply hw.2
    simp [h, fordShiftedDetectorPhysicalSingularities]
  have hwOne : w ≠ 1 := by
    intro h
    apply hw.2
    simp [h, fordShiftedDetectorPhysicalSingularities]
  have hgeom :=
    (mem_fordShiftedDetectorPhysicalRectangle_iff heta.le hy).mp hw.1
  have hweight : DifferentiableAt ℂ
      (fun z : ℂ => fordCotKernel eta
        (z - fordShiftedDetectorCenter sigma t)) w := by
    have hre :
        |(w - fordShiftedDetectorCenter sigma t).re| ≤ eta := by
      simpa [fordShiftedDetectorCenter] using hgeom.1
    exact differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hwCenter
  have hsur : sharpZetaSurrogate w ≠ 0 := by
    intro hzero
    have hzeta : riemannZeta w = 0 :=
      (sharpZetaSurrogate_eq_zero_iff hwOne).mp hzero
    have hmem : w ∈
        fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper :=
      mem_fordShiftedDetectorPhysicalZeros_of_rectangle
        heta.le hy hleft hw.1 hzeta
    apply hw.2
    simp [fordShiftedDetectorPhysicalSingularities, hmem]
  have hL : DifferentiableAt ℂ fordDetectorZetaLogDeriv w := by
    unfold fordDetectorZetaLogDeriv
    exact (differentiableAt_logDeriv_sharpZetaSurrogate hsur).sub
      ((differentiableAt_const (c := (1 : ℂ))).div
        (differentiableAt_id.sub_const (1 : ℂ))
        (sub_ne_zero.mpr hwOne))
  exact (hweight.mul hL).differentiableWithinAt

theorem fordZetaShiftedDetectorIntegrand_ne_physical_singularity
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (ht : 0 < t) (hPole : sigma - 1 ≤ eta)
    {p : ℂ} (hp : p ∈ fordShiftedDetectorPhysicalSingularities
      sigma eta t yLower yUpper) :
    ((fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t)) - fun s =>
      fordShiftedDetectorResidueCoefficient sigma eta t p / (s - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hcenterOne : fordShiftedDetectorCenter sigma t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordShiftedDetectorCenter] at him
    linarith
  simp only [fordShiftedDetectorPhysicalSingularities,
    Finset.mem_insert] at hp
  rcases hp with hcenter | hone | hp
  · subst p
    have hzeta : riemannZeta (fordShiftedDetectorCenter sigma t) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simpa using hsigma)
    simpa [fordShiftedDetectorResidueCoefficient] using
      fordZetaDetectorIntegrand_near_center heta hcenterOne hzeta
  · subst p
    have hre :
        |((1 : ℂ) - fordShiftedDetectorCenter sigma t).re| ≤ eta := by
      simp [fordShiftedDetectorCenter]
      rw [abs_of_nonpos]
      · linarith
      · linarith
    have hweight := differentiableAt_fordCotKernel_translate_of_abs_re_le
      heta hre hcenterOne.symm
    simpa [fordShiftedDetectorResidueCoefficient, hcenterOne.symm] using
      fordZetaDetectorIntegrand_near_one hweight
  · have hd := mem_fordShiftedDetectorPhysicalZeros_data hp
    have hpCenter : p ≠ fordShiftedDetectorCenter sigma t := by
      intro h
      subst p
      exact (riemannZeta_ne_zero_of_one_le_re
        (by simpa using hsigma)) hd.1
    have hpOne : p ≠ 1 := by
      intro h
      subst p
      exact riemannZeta_one_ne_zero hd.1
    have hweight :=
      differentiableAt_fordCotKernel_translate_at_shiftedPhysicalZero
        (t := t) hsigma heta hp
    simpa [fordShiftedDetectorResidueCoefficient, hpCenter, hpOne] using
      fordZetaDetectorIntegrand_near_zero hd.1 hweight

theorem fordZetaShiftedDetector_physicalRectangleIntegral_eq_residue_sum
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (ht : 0 < t) (hPole : sigma - 1 < eta)
    (hyLower : yLower < 0) (hytLower : yLower < t)
    (hytUpper : t < yUpper) (hleft : -1 ≤ sigma - eta)
    (hboundary : ∀ rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper,
      |rho.re - sigma| < eta ∧
        yLower < rho.im ∧ rho.im < yUpper) :
    RectangleIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (fordShiftedDetectorPhysicalLower sigma eta yLower)
      (fordShiftedDetectorPhysicalUpper sigma eta yUpper) =
      ∑ p ∈ fordShiftedDetectorPhysicalSingularities
        sigma eta t yLower yUpper,
        fordShiftedDetectorResidueCoefficient sigma eta t p := by
  have hy : yLower < yUpper := hytLower.trans hytUpper
  apply residueTheorem_finset
      (S := fordShiftedDetectorPhysicalSingularities
        sigma eta t yLower yUpper)
      (A := fordShiftedDetectorResidueCoefficient sigma eta t)
  · simp [fordShiftedDetectorPhysicalLower,
      fordShiftedDetectorPhysicalUpper]
    linarith
  · simp [fordShiftedDetectorPhysicalLower,
      fordShiftedDetectorPhysicalUpper]
    linarith
  · exact fordShiftedDetectorPhysicalSingularities_mem_nhds
      hsigma heta hPole hyLower (ht.trans hytUpper)
      hytLower hytUpper hboundary
  · exact
      fordZetaShiftedDetectorIntegrand_holomorphicOn_physicalRectangle_diff
        heta hy.le hleft
  · intro p hp
    exact fordZetaShiftedDetectorIntegrand_ne_physical_singularity
      hsigma heta ht hPole.le hp

theorem sum_fordShiftedDetectorPhysicalResidueCoefficient
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (ht : 0 < t) :
    (∑ p ∈ fordShiftedDetectorPhysicalSingularities
        sigma eta t yLower yUpper,
        fordShiftedDetectorResidueCoefficient sigma eta t p) =
      fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t) -
        fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t) +
        ∑ rho ∈ fordShiftedDetectorPhysicalZeros
            sigma eta yLower yUpper,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta
              (rho - fordShiftedDetectorCenter sigma t) := by
  classical
  have hcenterOne : fordShiftedDetectorCenter sigma t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [fordShiftedDetectorCenter] at him
    linarith
  have honeZero : (1 : ℂ) ∉
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper := by
    intro h
    exact riemannZeta_one_ne_zero
      (mem_fordShiftedDetectorPhysicalZeros_data h).1
  have hcenterZero : fordShiftedDetectorCenter sigma t ∉
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper := by
    intro h
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simpa using hsigma))
      (mem_fordShiftedDetectorPhysicalZeros_data h).1
  rw [fordShiftedDetectorPhysicalSingularities, Finset.sum_insert]
  · rw [Finset.sum_insert honeZero]
    simp only [fordShiftedDetectorResidueCoefficient, if_pos]
    have hsum :
        (∑ p ∈ fordShiftedDetectorPhysicalZeros
            sigma eta yLower yUpper,
          if p = fordShiftedDetectorCenter sigma t then
            fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t)
          else if p = 1 then
            -fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t)
          else (analyticVanishingOrder riemannZeta p : ℂ) *
            fordCotKernel eta
              (p - fordShiftedDetectorCenter sigma t)) =
          ∑ p ∈ fordShiftedDetectorPhysicalZeros
              sigma eta yLower yUpper,
            (analyticVanishingOrder riemannZeta p : ℂ) *
              fordCotKernel eta
                (p - fordShiftedDetectorCenter sigma t) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpCenter : p ≠ fordShiftedDetectorCenter sigma t := fun h =>
        hcenterZero (h ▸ hp)
      have hpOne : p ≠ 1 := fun h => honeZero (h ▸ hp)
      simp [hpCenter, hpOne]
    rw [hsum, if_neg hcenterOne.symm]
    ring
  · simp [hcenterOne, hcenterZero]

theorem fordZetaShiftedDetector_physicalRectangleIntegral_eq_explicit_sum
    {sigma eta t yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta) (ht : 0 < t) (hPole : sigma - 1 < eta)
    (hyLower : yLower < 0) (hytLower : yLower < t)
    (hytUpper : t < yUpper) (hleft : -1 ≤ sigma - eta)
    (hboundary : ∀ rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper,
      |rho.re - sigma| < eta ∧
        yLower < rho.im ∧ rho.im < yUpper) :
    RectangleIntegral'
      (fordZetaDetectorIntegrand eta
        (fordShiftedDetectorCenter sigma t))
      (fordShiftedDetectorPhysicalLower sigma eta yLower)
      (fordShiftedDetectorPhysicalUpper sigma eta yUpper) =
      fordDetectorZetaLogDeriv (fordShiftedDetectorCenter sigma t) -
        fordCotKernel eta (1 - fordShiftedDetectorCenter sigma t) +
        ∑ rho ∈ fordShiftedDetectorPhysicalZeros
            sigma eta yLower yUpper,
          (analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta
              (rho - fordShiftedDetectorCenter sigma t) := by
  rw [fordZetaShiftedDetector_physicalRectangleIntegral_eq_residue_sum
      hsigma heta ht hPole hyLower hytLower hytUpper hleft hboundary,
    sum_fordShiftedDetectorPhysicalResidueCoefficient hsigma ht]

end

end GafniTao
