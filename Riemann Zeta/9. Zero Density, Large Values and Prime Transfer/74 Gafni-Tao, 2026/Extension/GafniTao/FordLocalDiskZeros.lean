import GafniTao.FordShiftedZeroDetectorPoleTerm

/-!
# Ford's local disk of zeta zeros

Ford's local zero-count lemma uses the zeros in the closed disk of radius
`R` about `1 + t i`, counted with analytic multiplicity.  This file defines
that exact finite object and proves that, for Ford's numerical detector
parameters, it is a subset of the physical zero set occurring in the
pole-corrected contour inequality.
-/

open Complex Finset Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The actual nontrivial zeta zeros in Ford's closed disk
`|1 + t i - rho| <= R`. -/
noncomputable def fordLocalDiskZeros (t R : ℝ) : Finset ℂ :=
  (zeroSet 0 (|t| + R)).filter fun rho =>
    ‖(1 : ℂ) + (t : ℂ) * I - rho‖ ≤ R

/-- Ford's `N(t,R)`, with analytic multiplicity. -/
noncomputable def fordLocalDiskZeroCount (t R : ℝ) : ℕ :=
  ∑ rho ∈ fordLocalDiskZeros t R,
    analyticVanishingOrder riemannZeta rho

theorem mem_fordLocalDiskZeros_iff {t R : ℝ} {rho : ℂ} :
    rho ∈ fordLocalDiskZeros t R ↔
      rho ∈ zeroSet 0 (|t| + R) ∧
        ‖(1 : ℂ) + (t : ℂ) * I - rho‖ ≤ R := by
  simp [fordLocalDiskZeros]

theorem mem_fordLocalDiskZeros_data {t R : ℝ} {rho : ℂ}
    (hrho : rho ∈ fordLocalDiskZeros t R) :
    riemannZeta rho = 0 ∧ 0 ≤ rho.re ∧ rho.re ≤ 1 ∧
      |1 - rho.re| ≤ R ∧ |t - rho.im| ≤ R := by
  have h := (mem_fordLocalDiskZeros_iff.mp hrho)
  have hz := mem_zeroSet_zero_data h.1
  have hreNorm : |1 - rho.re| ≤
      ‖(1 : ℂ) + (t : ℂ) * I - rho‖ := by
    simpa using abs_re_le_norm ((1 : ℂ) + (t : ℂ) * I - rho)
  have himNorm : |t - rho.im| ≤
      ‖(1 : ℂ) + (t : ℂ) * I - rho‖ := by
    simpa using abs_im_le_norm ((1 : ℂ) + (t : ℂ) * I - rho)
  exact ⟨hz.2.2.2.2, hz.1, hz.2.1,
    hreNorm.trans h.2, himNorm.trans h.2⟩

/-- A geometric disk-to-rectangle bridge.  The hypotheses expose every
endpoint comparison needed by the detector's physical finite rectangle. -/
theorem fordLocalDiskZeros_subset_physical
    {sigma eta t R yLower yUpper : ℝ}
    (hreLower : sigma - eta ≤ 1 - R)
    (hreUpper : 1 ≤ sigma + eta)
    (himLower : yLower ≤ t - R)
    (himUpper : t + R ≤ yUpper) :
    fordLocalDiskZeros t R ⊆
      fordShiftedDetectorPhysicalZeros
        sigma eta yLower yUpper := by
  intro rho hrho
  have hd := mem_fordLocalDiskZeros_data hrho
  have hreDisk := abs_le.mp hd.2.2.2.1
  have himDisk := abs_le.mp hd.2.2.2.2
  have hreBounds : sigma - eta ≤ rho.re ∧ rho.re ≤ sigma + eta := by
    constructor
    · linarith
    · linarith
  have himBounds : yLower ≤ rho.im ∧ rho.im ≤ yUpper := by
    constructor <;> linarith
  have hheight : |rho.im| ≤ max |yLower| |yUpper| := by
    rw [abs_le]
    constructor
    · calc
        -max |yLower| |yUpper| ≤ -|yLower| :=
          neg_le_neg (le_max_left _ _)
        _ ≤ yLower := neg_abs_le _
        _ ≤ rho.im := himBounds.1
    · calc
        rho.im ≤ yUpper := himBounds.2
        _ ≤ |yUpper| := le_abs_self _
        _ ≤ max |yLower| |yUpper| := le_max_right _ _
  have hzeroSet : rho ∈ zeroSet 0 (max |yLower| |yUpper|) := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      0 1 (-max |yLower| |yUpper|) (max |yLower| |yUpper|)
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff]
    refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
      0 1 (-max |yLower| |yUpper|)
        (max |yLower| |yUpper|) rho).mpr ?_, hd.1⟩
    exact ⟨hd.2.1, hd.2.2.1, (abs_le.mp hheight).1,
      (abs_le.mp hheight).2⟩
  rw [mem_fordShiftedDetectorPhysicalZeros_iff]
  refine ⟨hzeroSet, ?_, himBounds⟩
  exact abs_le.mpr ⟨by linarith [hreBounds.1], by linarith [hreBounds.2]⟩

/-- The exact numerical specialization used in Ford's local-zero lemma:
`sigma = 1 + 0.6421 R` and `eta = 2.5 R`. -/
theorem fordLocalDiskZeros_subset_physical_fordParameters
    {t R yLower yUpper : ℝ}
    (hR : 0 ≤ R)
    (himLower : yLower ≤ t - R)
    (himUpper : t + R ≤ yUpper) :
    fordLocalDiskZeros t R ⊆
      fordShiftedDetectorPhysicalZeros
        (1 + (6421 / 10000 : ℝ) * R) ((5 / 2 : ℝ) * R)
        yLower yUpper := by
  apply fordLocalDiskZeros_subset_physical
  · nlinarith
  · nlinarith
  · exact himLower
  · exact himUpper

theorem fordLocalDiskZeroCount_eq_weighted_sum (t R : ℝ) :
    fordLocalDiskZeroCount t R =
      ∑ rho ∈ fordLocalDiskZeros t R,
        analyticVanishingOrder riemannZeta rho := rfl

end

end GafniTao
