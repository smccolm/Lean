import GafniTao.FordZeroDetectorDifferentiability
import GafniTao.SharpPerronRectangle

/-!
# Ford's zero-detector rectangle at a shifted real centre

Ford's local zero-count argument applies the cotangent detector at
`sigma + it`, not only at `1 + it`.  This module supplies the missing exact
geometric layer.  The finite zero set contains the actual nontrivial zeta
zeros in the shifted rectangle; analytic multiplicity is attached by the
residue theorem in the next module.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

noncomputable def fordShiftedDetectorCenter (sigma t : ℝ) : ℂ :=
  (sigma : ℂ) + (t : ℂ) * I

noncomputable def fordShiftedDetectorLower
    (sigma eta t R : ℝ) : ℂ :=
  ((sigma - eta : ℝ) : ℂ) + ((t - R : ℝ) : ℂ) * I

noncomputable def fordShiftedDetectorUpper
    (sigma eta t R : ℝ) : ℂ :=
  ((sigma + eta : ℝ) : ℂ) + ((t + R : ℝ) : ℂ) * I

noncomputable def fordShiftedDetectorZeros
    (sigma eta t R : ℝ) : Finset ℂ :=
  (zeroSet 0 (|t| + R)).filter fun rho =>
    |rho.re - sigma| ≤ eta ∧ |rho.im - t| ≤ R

@[simp] theorem fordShiftedDetectorCenter_re (sigma t : ℝ) :
    (fordShiftedDetectorCenter sigma t).re = sigma := by
  simp [fordShiftedDetectorCenter]

@[simp] theorem fordShiftedDetectorCenter_im (sigma t : ℝ) :
    (fordShiftedDetectorCenter sigma t).im = t := by
  simp [fordShiftedDetectorCenter]

theorem mem_fordShiftedDetectorRectangle_iff
    {sigma eta t R : ℝ} (heta : 0 ≤ eta) (hR : 0 ≤ R) {z : ℂ} :
    z ∈ Rectangle (fordShiftedDetectorLower sigma eta t R)
        (fordShiftedDetectorUpper sigma eta t R) ↔
      |z.re - sigma| ≤ eta ∧ |z.im - t| ≤ R := by
  rw [Rectangle, mem_reProdIm]
  simp only [fordShiftedDetectorLower, fordShiftedDetectorUpper, add_re,
    ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
    add_im, mul_im, mul_one, zero_add]
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  simp only [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem mem_fordShiftedDetectorZeros_iff
    {sigma eta t R : ℝ} {rho : ℂ} :
    rho ∈ fordShiftedDetectorZeros sigma eta t R ↔
      rho ∈ zeroSet 0 (|t| + R) ∧
        |rho.re - sigma| ≤ eta ∧ |rho.im - t| ≤ R := by
  simp [fordShiftedDetectorZeros]

theorem mem_fordShiftedDetectorZeros_of_rectangle
    {sigma eta t R : ℝ} (heta : 0 ≤ eta) (hR : 0 ≤ R)
    (hleft : -1 ≤ sigma - eta) {rho : ℂ}
    (hrhoRect : rho ∈ Rectangle
      (fordShiftedDetectorLower sigma eta t R)
      (fordShiftedDetectorUpper sigma eta t R))
    (hrhoZero : riemannZeta rho = 0) :
    rho ∈ fordShiftedDetectorZeros sigma eta t R := by
  have hgeom :=
    (mem_fordShiftedDetectorRectangle_iff heta hR).mp hrhoRect
  have hrhoLeft : -1 ≤ rho.re := by
    have := (abs_le.mp hgeom.1).1
    linarith
  have hstrip := zeta_zero_re_mem_of_neg_one_le hrhoLeft hrhoZero
  have himAbs : |rho.im| ≤ |t| + R := by
    have hdiff := abs_le.mp hgeom.2
    apply abs_le.mpr
    constructor
    · have ht : -|t| ≤ t := neg_abs_le t
      linarith
    · calc
        rho.im ≤ t + R := by linarith
        _ ≤ |t| + R := by linarith [le_abs_self t]
  have hzeroSet : rho ∈ zeroSet 0 (|t| + R) := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (- (|t| + R)) (|t| + R)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
      0 1 (- (|t| + R)) (|t| + R) rho).mpr ?_, hrhoZero⟩
    exact ⟨hstrip.1, hstrip.2, (abs_le.mp himAbs).1,
      (abs_le.mp himAbs).2⟩
  exact (mem_fordShiftedDetectorZeros_iff).mpr ⟨hzeroSet, hgeom⟩

theorem mem_fordShiftedDetectorZeros_data
    {sigma eta t R : ℝ} {rho : ℂ}
    (hrho : rho ∈ fordShiftedDetectorZeros sigma eta t R) :
    riemannZeta rho = 0 ∧
      |rho.re - sigma| ≤ eta ∧ |rho.im - t| ≤ R := by
  have h := mem_fordShiftedDetectorZeros_iff.mp hrho
  exact ⟨(mem_zeroSet_zero_data h.1).2.2.2.2, h.2⟩

theorem differentiableAt_fordCotKernel_translate_at_shiftedDetectorZero
    {sigma eta t R : ℝ} (hsigma : 1 ≤ sigma) (heta : 0 < eta)
    {rho : ℂ} (hrho : rho ∈ fordShiftedDetectorZeros sigma eta t R) :
    DifferentiableAt ℂ
      (fun w : ℂ => fordCotKernel eta
        (w - fordShiftedDetectorCenter sigma t)) rho := by
  have hd := mem_fordShiftedDetectorZeros_data hrho
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

end

end GafniTao
