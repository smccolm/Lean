import GafniTao.FordZeroDetectorDifferentiability
import GafniTao.SharpPerronRectangle

/-!
# The finite Ford zero-detector rectangle

This file fixes the physical center `1+it`, defines the literal finite set of
nontrivial zeros in the rectangle of half-widths `η,R`, and proves that every
zeta zero of the geometric rectangle is captured by that finite set.  No
distinct-zero proxy is used: multiplicity remains attached later through
`analyticVanishingOrder`.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

noncomputable def fordDetectorCenter (t : ℝ) : ℂ :=
  (1 : ℂ) + (t : ℂ) * I

noncomputable def fordDetectorLower (eta t R : ℝ) : ℂ :=
  ((1 - eta : ℝ) : ℂ) + ((t - R : ℝ) : ℂ) * I

noncomputable def fordDetectorUpper (eta t R : ℝ) : ℂ :=
  ((1 + eta : ℝ) : ℂ) + ((t + R : ℝ) : ℂ) * I

/-- The actual finite nontrivial-zero set in Ford's rectangle. -/
noncomputable def fordDetectorZeros (eta t R : ℝ) : Finset ℂ :=
  (zeroSet 0 (|t| + R)).filter fun rho =>
    |rho.re - 1| ≤ eta ∧ |rho.im - t| ≤ R

theorem fordDetectorCenter_re (t : ℝ) : (fordDetectorCenter t).re = 1 := by
  simp [fordDetectorCenter]

theorem fordDetectorCenter_im (t : ℝ) : (fordDetectorCenter t).im = t := by
  simp [fordDetectorCenter]

theorem mem_fordDetectorRectangle_iff
    {eta t R : ℝ} (heta : 0 ≤ eta) (hR : 0 ≤ R) {z : ℂ} :
    z ∈ Rectangle (fordDetectorLower eta t R)
        (fordDetectorUpper eta t R) ↔
      |z.re - 1| ≤ eta ∧ |z.im - t| ≤ R := by
  rw [Rectangle, mem_reProdIm]
  simp only [fordDetectorLower, fordDetectorUpper, add_re, ofReal_re,
    mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
    add_im, mul_im, mul_one, zero_add]
  rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
  simp only [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨hl, hu⟩, hli, hui⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem mem_fordDetectorZeros_iff
    {eta t R : ℝ} {rho : ℂ} :
    rho ∈ fordDetectorZeros eta t R ↔
      rho ∈ zeroSet 0 (|t| + R) ∧
        |rho.re - 1| ≤ eta ∧ |rho.im - t| ≤ R := by
  simp [fordDetectorZeros]

/-- Every zeta zero in the geometric detector rectangle belongs to the
literal finite detector zero set. -/
theorem mem_fordDetectorZeros_of_rectangle
    {eta t R : ℝ} (heta : 0 ≤ eta) (hetaUpper : eta ≤ 1)
    (hR : 0 ≤ R) {rho : ℂ}
    (hrhoRect : rho ∈ Rectangle (fordDetectorLower eta t R)
      (fordDetectorUpper eta t R))
    (hrhoZero : riemannZeta rho = 0) :
    rho ∈ fordDetectorZeros eta t R := by
  have hgeom := (mem_fordDetectorRectangle_iff heta hR).mp hrhoRect
  have hleft : -1 ≤ rho.re := by
    have := (abs_le.mp hgeom.1).1
    linarith
  have hstrip := zeta_zero_re_mem_of_neg_one_le hleft hrhoZero
  have himAbs : |rho.im| ≤ |t| + R := by
    have hdiff := (abs_le.mp hgeom.2)
    have hupper : rho.im ≤ |t| + R := by
      calc
        rho.im ≤ t + R := by linarith
        _ ≤ |t| + R := by linarith [le_abs_self t]
    have hlower : -(|t| + R) ≤ rho.im := by
      have ht : -|t| ≤ t := neg_abs_le t
      linarith
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hzeroSet : rho ∈ zeroSet 0 (|t| + R) := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (- (|t| + R)) (|t| + R)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
      0 1 (- (|t| + R)) (|t| + R) rho).mpr ?_, hrhoZero⟩
    exact ⟨hstrip.1, hstrip.2, (abs_le.mp himAbs).1,
      (abs_le.mp himAbs).2⟩
  exact (mem_fordDetectorZeros_iff).mpr ⟨hzeroSet, hgeom⟩

/-- Membership in the detector zero set recovers both the actual zeta-zero
fact and the geometric bounds. -/
theorem mem_fordDetectorZeros_data
    {eta t R : ℝ} {rho : ℂ} (hrho : rho ∈ fordDetectorZeros eta t R) :
    riemannZeta rho = 0 ∧
      |rho.re - 1| ≤ eta ∧ |rho.im - t| ≤ R := by
  have h := (mem_fordDetectorZeros_iff.mp hrho)
  exact ⟨(mem_zeroSet_zero_data h.1).2.2.2.2, h.2⟩

/-- Every detector zero distinct from the center has an analytic translated
cotangent weight.  A genuine zero can never equal the center because zeta is
nonzero on `Re s = 1`. -/
theorem differentiableAt_fordCotKernel_translate_at_detectorZero
    {eta t R : ℝ} (heta : 0 < eta) {rho : ℂ}
    (hrho : rho ∈ fordDetectorZeros eta t R) :
    DifferentiableAt ℂ
      (fun w : ℂ => fordCotKernel eta (w - fordDetectorCenter t)) rho := by
  have hd := mem_fordDetectorZeros_data hrho
  have hcenter : rho ≠ fordDetectorCenter t := by
    intro h
    subst rho
    exact (riemannZeta_ne_zero_of_one_le_re
      (by simp [fordDetectorCenter])) hd.1
  have hre : |(rho - fordDetectorCenter t).re| ≤ eta := by
    simpa [fordDetectorCenter] using hd.2.1
  exact differentiableAt_fordCotKernel_translate_of_abs_re_le
    heta hre hcenter

end

end GafniTao
