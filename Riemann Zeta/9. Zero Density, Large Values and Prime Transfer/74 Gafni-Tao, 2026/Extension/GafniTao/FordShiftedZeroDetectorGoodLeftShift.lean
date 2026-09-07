import GafniTao.FordShiftedZeroDetectorAsymmetricAssembly
import GafniTao.FordZeroDetectorGoodLeftShift

/-!
# Good left edges for the shifted Ford detector

The bad shifts are the differences between sigma and the real parts of the
finitely many zeros in the physical height box.  Avoiding this finite set
supplies a genuine zero-free left boundary.
-/

open Complex Set Finset
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

noncomputable def fordShiftedDetectorBadLeftShifts
    (sigma H : ℝ) : Finset ℝ :=
  (zeroSet 0 H).image fun rho => sigma - rho.re

theorem mem_fordShiftedDetectorBadLeftShifts
    {sigma H : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSet 0 H) :
    sigma - rho.re ∈ fordShiftedDetectorBadLeftShifts sigma H := by
  exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩

theorem exists_fordShiftedDetector_shift_avoiding_zeros
    {sigma eta etaMax H : ℝ} (heta : eta < etaMax) :
    ∃ eta' : ℝ, eta < eta' ∧ eta' < etaMax ∧
      ∀ rho ∈ zeroSet 0 H, eta' ≠ sigma - rho.re := by
  classical
  obtain ⟨eta', hetaLow, hetaHigh, havoid⟩ :=
    exists_interval_point_not_mem_finset
      (fordShiftedDetectorBadLeftShifts sigma H) heta
  refine ⟨eta', hetaLow, hetaHigh, ?_⟩
  intro rho hrho
  exact havoid (sigma - rho.re)
    (mem_fordShiftedDetectorBadLeftShifts hrho)

theorem exists_fordShiftedDetector_good_left_shift
    {sigma eta etaMax yLower yUpper : ℝ}
    (heta : 0 ≤ eta) (hetaMax : eta < etaMax)
    (hleftMax : -1 ≤ sigma - etaMax)
    (hy : yLower ≤ yUpper) :
    ∃ eta' : ℝ, eta < eta' ∧ eta' < etaMax ∧
      ∀ y ∈ Set.Icc yLower yUpper,
        riemannZeta
          (((sigma - eta' : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
  let H : ℝ := max |yLower| |yUpper|
  obtain ⟨eta', hetaLow, hetaHigh, havoid⟩ :=
    exists_fordShiftedDetector_shift_avoiding_zeros
      (sigma := sigma) (H := H) hetaMax
  have heta'0 : 0 ≤ eta' := by linarith
  have hleft' : -1 ≤ sigma - eta' := by linarith
  refine ⟨eta', hetaLow, hetaHigh, ?_⟩
  intro y hyIcc hzeta
  let rho : ℂ :=
    ((sigma - eta' : ℝ) : ℂ) + (y : ℂ) * I
  have hrhoRect : rho ∈ Rectangle
      (fordShiftedDetectorPhysicalLower sigma eta' yLower)
      (fordShiftedDetectorPhysicalUpper sigma eta' yUpper) := by
    rw [mem_fordShiftedDetectorPhysicalRectangle_iff heta'0 hy]
    dsimp [rho]
    simp only [ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, mul_im, mul_one, zero_add]
    constructor
    · simp [abs_of_nonneg heta'0]
    · simpa using hyIcc
  have hrhoMem : rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta' yLower yUpper :=
    mem_fordShiftedDetectorPhysicalZeros_of_rectangle
      heta'0 hy hleft' hrhoRect hzeta
  have hrhoZeroSet : rho ∈ zeroSet 0 H :=
    (mem_fordShiftedDetectorPhysicalZeros_iff.mp hrhoMem).1
  apply havoid rho hrhoZeroSet
  dsimp [rho]
  simp

theorem fordShiftedDetectorPhysicalZeros_strict_of_edge_nonvanishing
    {sigma eta yLower yUpper : ℝ} (hsigma : 1 ≤ sigma)
    (heta : 0 < eta)
    (hzetaLeft : ∀ y ∈ Set.Icc yLower yUpper,
      riemannZeta
        (((sigma - eta : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hzetaTop : ∀ x ∈ Set.Icc (sigma - eta) (sigma + eta),
      riemannZeta ((x : ℂ) + (yUpper : ℂ) * I) ≠ 0)
    (hzetaBottom : ∀ x ∈ Set.Icc (sigma - eta) (sigma + eta),
      riemannZeta ((x : ℂ) + (yLower : ℂ) * I) ≠ 0) :
    ∀ rho ∈
      fordShiftedDetectorPhysicalZeros sigma eta yLower yUpper,
      |rho.re - sigma| < eta ∧
        yLower < rho.im ∧ rho.im < yUpper := by
  intro rho hrho
  have hd := mem_fordShiftedDetectorPhysicalZeros_data hrho
  have hreBounds := abs_le.mp hd.2.1
  have himBounds := hd.2.2
  have hreIcc :
      rho.re ∈ Set.Icc (sigma - eta) (sigma + eta) := by
    constructor <;> linarith
  have hleftStrict : sigma - eta < rho.re := by
    apply lt_of_le_of_ne (by linarith [hreBounds.1])
    intro heq
    apply hzetaLeft rho.im ⟨himBounds.1, himBounds.2⟩
    calc
      riemannZeta
          (((sigma - eta : ℝ) : ℂ) + (rho.im : ℂ) * I) =
          riemannZeta rho := congrArg riemannZeta
            (Complex.ext (by simpa using heq) (by simp))
      _ = 0 := hd.1
  have hrightStrict : rho.re < sigma + eta := by
    have hrightNonzero :
        riemannZeta
          (((sigma + eta : ℝ) : ℂ) + (rho.im : ℂ) * I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp
      linarith
    apply lt_of_le_of_ne (by linarith [hreBounds.2])
    intro heq
    apply hrightNonzero
    calc
      riemannZeta
          (((sigma + eta : ℝ) : ℂ) + (rho.im : ℂ) * I) =
          riemannZeta rho := congrArg riemannZeta
            (Complex.ext (by simpa using heq.symm) (by simp))
      _ = 0 := hd.1
  have hbottomStrict : yLower < rho.im := by
    apply lt_of_le_of_ne himBounds.1
    intro heq
    apply hzetaBottom rho.re hreIcc
    calc
      riemannZeta ((rho.re : ℂ) + (yLower : ℂ) * I) =
          riemannZeta rho := congrArg riemannZeta
            (Complex.ext (by simp) (by simpa using heq))
      _ = 0 := hd.1
  have htopStrict : rho.im < yUpper := by
    apply lt_of_le_of_ne himBounds.2
    intro heq
    apply hzetaTop rho.re hreIcc
    calc
      riemannZeta ((rho.re : ℂ) + (yUpper : ℂ) * I) =
          riemannZeta rho := congrArg riemannZeta
            (Complex.ext (by simp) (by simpa using heq.symm))
      _ = 0 := hd.1
  exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩,
    hbottomStrict, htopStrict⟩

end

end GafniTao
