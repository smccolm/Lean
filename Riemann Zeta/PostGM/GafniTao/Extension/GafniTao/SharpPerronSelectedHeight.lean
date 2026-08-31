import GafniTao.SharpPerronLeftEdge
import GafniTao.SharpPerronLogBound

/-!
# A residue-compatible selected Perron height

The good-height separation used for the horizontal logarithmic derivative
also excludes zeta zeros from both horizontal sides of the residue
rectangle.  This closes the strict-boundary hypothesis of the rectangle
residue theorem rather than assuming it separately.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

theorem sharpPerron_good_height_zeroSet_strict
    {T R : ℝ} (hT : 8 ≤ T) (hR : R ∈ Set.Icc T (T + 1))
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ∀ rho ∈ zeroSet 0 R, |rho.im| < R := by
  intro rho hrho
  have hd := mem_zeroSet_zero_data hrho
  have hRpos : 0 < R := by linarith [hR.1]
  have habsLe : |rho.im| ≤ R := (abs_le).2 ⟨hd.2.2.1, hd.2.2.2.1⟩
  apply lt_of_le_of_ne habsLe
  intro heq
  have habsEq : |rho.im| = |R| := by
    rw [abs_of_pos hRpos]
    exact heq
  rcases eq_or_eq_neg_of_abs_eq habsEq with him | him
  · have him' : rho.im = R := by simpa [abs_of_pos hRpos] using him
    have hzetaNe := sharpPerron_extended_positive_zeta_ne_zero
      (σ := rho.re)
      hT hR (by linarith [hd.1]) hfar
    have hrhoEq : rho = (rho.re : ℂ) + (R : ℂ) * I := by
      apply Complex.ext
      · simp
      · simpa using him'
    apply hzetaNe
    rw [← hrhoEq]
    exact hd.2.2.2.2
  · have him' : rho.im = -R := by simpa [abs_of_pos hRpos] using him
    have hzetaNe := sharpPerron_extended_negative_zeta_ne_zero
      (σ := rho.re)
      hT hR (by linarith [hd.1]) hfar
    have hrhoEq : rho = (rho.re : ℂ) - (R : ℂ) * I := by
      apply Complex.ext
      · simp
      · simpa using him'
    apply hzetaNe
    rw [← hrhoEq]
    exact hd.2.2.2.2

/-- A good height in `[T,T+1]` simultaneously supplies the horizontal-edge
separation and the strict residue-rectangle boundary condition. -/
theorem exists_sharpPerron_residue_good_height
    {T : ℝ} (hT : 8 ≤ T) :
    ∃ R : ℝ, R ∈ Set.Icc T (T + 1) ∧
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) ∧
      (∀ rho ∈ zeroSet 0 R, |rho.im| < R) := by
  obtain ⟨R, hRlow, hRhigh, hfar⟩ := exists_sharpPerron_good_height hT
  have hR : R ∈ Set.Icc T (T + 1) := ⟨hRlow, hRhigh⟩
  exact ⟨R, hR, hfar,
    sharpPerron_good_height_zeroSet_strict hT hR hfar⟩

end GafniTao
