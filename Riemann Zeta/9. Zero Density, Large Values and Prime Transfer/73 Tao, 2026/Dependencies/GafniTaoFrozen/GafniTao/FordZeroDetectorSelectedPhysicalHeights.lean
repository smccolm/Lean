import GafniTao.FordZeroDetectorAsymmetricAssembly
import GafniTao.FordZeroDetectorHorizontalBound
import GafniTao.SharpPerronSelectedHeight
import GafniTao.SharpPerronHorizontalIntegrand

/-!
# Independent Landau heights for Ford's translated detector

The upper physical ordinate and the absolute value of the lower physical
ordinate are selected independently.  This is the exact interface needed by
the asymmetric detector rectangle.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem fordHorizontalPoint_at_positive_physical_height
    (t R x : ℝ) :
    fordHorizontalPoint t (R - t) x =
      (x : ℂ) + (R : ℂ) * I := by
  unfold fordHorizontalPoint
  push_cast
  ring

theorem fordHorizontalPoint_at_negative_physical_height
    (t R x : ℝ) :
    fordHorizontalPoint t (-R - t) x =
      (x : ℂ) - (R : ℂ) * I := by
  unfold fordHorizontalPoint
  push_cast
  ring

theorem riemannZeta_ne_zero_of_nonpos_re_nonzero_im
    {s : ℂ} (hre : s.re ≤ 0) (him : s.im ≠ 0) :
    riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    apply him
    simp [h]
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have href : riemannZeta (1 - s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
    linarith
  exact riemannZeta_ne_zero_of_reflected hs0 h1s0
    (Gammaℝ_ne_zero_of_im_ne_zero him) href

theorem fordHorizontalLogDeriv_positive_physical_le
    {C T t x R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hx : -1 ≤ x)
    (hfar : ∀ rho ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T rho).im|)
    (hlog : ∀ {T sigma R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → -1 ≤ sigma →
      (∀ rho ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T rho).im|) →
      ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * I)‖ ≤
        C * Real.log T ^ 2) :
    ‖fordHorizontalLogDeriv t (R - t) x‖ ≤ C * Real.log T ^ 2 := by
  have hzeta := sharpPerron_extended_positive_zeta_ne_zero
    hT hR hx hfar
  have hRpos : 0 < R := by linarith [hR.1]
  have hone : (x : ℂ) + (R : ℂ) * I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hRpos.ne' him
  unfold fordHorizontalLogDeriv
  rw [fordHorizontalPoint_at_positive_physical_height,
    fordDetectorZetaLogDeriv_eq hone hzeta, logDeriv_apply]
  exact hlog hT hR hx hfar

theorem fordHorizontalLogDeriv_negative_physical_le
    {C T t x R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hx : -1 ≤ x)
    (hfar : ∀ rho ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T rho).im|)
    (hlog : ∀ {T sigma R : ℝ} (hT : 8 ≤ T),
      R ∈ Set.Icc T (T + 1) → -1 ≤ sigma →
      (∀ rho ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T rho).im|) →
      ‖deriv riemannZeta ((sigma : ℂ) - (R : ℂ) * I) /
        riemannZeta ((sigma : ℂ) - (R : ℂ) * I)‖ ≤
        C * Real.log T ^ 2) :
    ‖fordHorizontalLogDeriv t (-R - t) x‖ ≤ C * Real.log T ^ 2 := by
  have hzeta := sharpPerron_extended_negative_zeta_ne_zero
    hT hR hx hfar
  have hRpos : 0 < R := by linarith [hR.1]
  have hone : (x : ℂ) - (R : ℂ) * I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hRpos.ne' him
  unfold fordHorizontalLogDeriv
  rw [fordHorizontalPoint_at_negative_physical_height,
    fordDetectorZetaLogDeriv_eq hone hzeta, logDeriv_apply]
  exact hlog hT hR hx hfar

/-- Simultaneous upper and lower physical good heights, with the actual zeta
nonvanishing and logarithmic-derivative estimates required by Ford's two
horizontal remainders. -/
theorem exists_fordDetector_independent_good_heights :
    ∃ C : ℝ, 0 < C ∧ ∀ {T t : ℝ} (_hT : 8 ≤ T),
      ∃ RUpper RLower : ℝ,
        RUpper ∈ Set.Icc T (T + 1) ∧
        RLower ∈ Set.Icc T (T + 1) ∧
        (∀ x : ℝ,
          riemannZeta (fordHorizontalPoint t (RUpper - t) x) ≠ 0) ∧
        (∀ x : ℝ,
          riemannZeta (fordHorizontalPoint t (-RLower - t) x) ≠ 0) ∧
        (∀ x : ℝ, -1 ≤ x →
          ‖fordHorizontalLogDeriv t (RUpper - t) x‖ ≤
            C * Real.log T ^ 2) ∧
        (∀ x : ℝ, -1 ≤ x →
          ‖fordHorizontalLogDeriv t (-RLower - t) x‖ ≤
            C * Real.log T ^ 2) := by
  obtain ⟨Cpos, hCpos, hpos⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_positive_horizontal_le
  obtain ⟨Cneg, hCneg, hneg⟩ :=
    exists_norm_riemannZeta_logDeriv_extended_negative_horizontal_le
  let C := max Cpos Cneg
  refine ⟨C, hCpos.trans_le (le_max_left _ _), ?_⟩
  intro T t _hT
  obtain ⟨RUpper, hRUpperLow, hRUpperHigh, hfarUpper⟩ :=
    exists_sharpPerron_good_height _hT
  obtain ⟨RLower, hRLowerLow, hRLowerHigh, hfarLower⟩ :=
    exists_sharpPerron_good_height _hT
  have hRU : RUpper ∈ Set.Icc T (T + 1) :=
    ⟨hRUpperLow, hRUpperHigh⟩
  have hRL : RLower ∈ Set.Icc T (T + 1) :=
    ⟨hRLowerLow, hRLowerHigh⟩
  refine ⟨RUpper, RLower, hRU, hRL, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [fordHorizontalPoint_at_positive_physical_height]
    by_cases hx : -1 ≤ x
    · exact sharpPerron_extended_positive_zeta_ne_zero
        _hT hRU hx hfarUpper
    · apply riemannZeta_ne_zero_of_nonpos_re_nonzero_im
      · simp
        linarith
      · simp
        linarith [hRU.1]
  · intro x
    rw [fordHorizontalPoint_at_negative_physical_height]
    by_cases hx : -1 ≤ x
    · exact sharpPerron_extended_negative_zeta_ne_zero
        _hT hRL hx hfarLower
    · apply riemannZeta_ne_zero_of_nonpos_re_nonzero_im
      · simp
        linarith
      · simp
        linarith [hRL.1]
  · intro x hx
    exact (fordHorizontalLogDeriv_positive_physical_le
      _hT hRU hx hfarUpper hpos).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (sq_nonneg _))
  · intro x hx
    exact (fordHorizontalLogDeriv_negative_physical_le
      _hT hRL hx hfarLower hneg).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (sq_nonneg _))

theorem fordDetectorPhysicalZeros_strict_of_edge_nonvanishing
    {eta yLower yUpper : ℝ} (heta : 0 < eta)
    (hzetaLeft : ∀ y ∈ Set.Icc yLower yUpper,
      riemannZeta (((1 - eta : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0)
    (hzetaTop : ∀ x ∈ Set.Icc (1 - eta) (1 + eta),
      riemannZeta ((x : ℂ) + (yUpper : ℂ) * I) ≠ 0)
    (hzetaBottom : ∀ x ∈ Set.Icc (1 - eta) (1 + eta),
      riemannZeta ((x : ℂ) + (yLower : ℂ) * I) ≠ 0) :
    ∀ rho ∈ fordDetectorPhysicalZeros eta yLower yUpper,
      |rho.re - 1| < eta ∧ yLower < rho.im ∧ rho.im < yUpper := by
  intro rho hrho
  have hd := mem_fordDetectorPhysicalZeros_data hrho
  have hreBounds := abs_le.mp hd.2.1
  have himBounds := hd.2.2
  have hreIcc : rho.re ∈ Set.Icc (1 - eta) (1 + eta) := by
    constructor <;> linarith
  have hleftStrict : 1 - eta < rho.re := by
    apply lt_of_le_of_ne (by linarith [hreBounds.1])
    intro heq
    apply hzetaLeft rho.im ⟨himBounds.1, himBounds.2⟩
    calc
      riemannZeta (((1 - eta : ℝ) : ℂ) + (rho.im : ℂ) * I) =
          riemannZeta rho := congrArg riemannZeta
            (Complex.ext (by simpa using heq) (by simp))
      _ = 0 := hd.1
  have hrightStrict : rho.re < 1 + eta := by
    have hrightNonzero :
        riemannZeta (((1 + eta : ℝ) : ℂ) + (rho.im : ℂ) * I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp
      linarith
    apply lt_of_le_of_ne (by linarith [hreBounds.2])
    intro heq
    apply hrightNonzero
    calc
      riemannZeta (((1 + eta : ℝ) : ℂ) + (rho.im : ℂ) * I) =
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
