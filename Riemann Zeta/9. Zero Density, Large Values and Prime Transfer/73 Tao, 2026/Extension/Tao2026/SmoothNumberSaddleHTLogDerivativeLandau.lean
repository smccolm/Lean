import Tao2026.SmoothNumberSaddleHTLogDerivativeSeparation
import GafniTao.SharpPerronPhysicalHorizontal

/-!
# Landau logarithmic derivative from VK separation

The frozen sharp-Perron logarithmic-derivative estimate selects a height to
separate the evaluation point vertically from nearby zeros.  The HT contour
cannot make that selection after the frequency translation.  Here the spare
Vinogradov--Korobov width supplies horizontal separation instead.

This module reruns the finite Landau zero-sum estimate with distance
`eta`, proves the corresponding point is outside the larger zero disk, and
instantiates the frozen `FinalBound` theorem.  The result is a pointwise
physical bound for `zeta'/zeta` at every positive height, without a selected
ordinate.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace Tao2026

noncomputable section

theorem norm_sharpLandau_zeroTerm_le_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hSigma : 1 - eta ≤ sigma)
    {rho : ℂ} (hrho : rho ∈ GafniTao.sharpLandauZeroFinset T hT) :
    ‖(analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℂ) /
        (GafniTao.sharpLandauCoord T sigma R - rho)‖ ≤
      (7 / (4 * eta)) *
        analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho := by
  have hsep := sharpLandauCoord_zero_separation_of_vK
    hZeroFree hT hHeight heta hWidth hSigma (R := R) hrho
  have hnorm : 0 < ‖GafniTao.sharpLandauCoord T sigma R - rho‖ := by
    nlinarith [norm_nonneg (GafniTao.sharpLandauCoord T sigma R - rho)]
  have hscale : 1 ≤ (7 / (4 * eta)) *
      ‖GafniTao.sharpLandauCoord T sigma R - rho‖ := by
    rw [show (7 / (4 * eta)) *
        ‖GafniTao.sharpLandauCoord T sigma R - rho‖ =
      ((7 / 4 : ℝ) *
        ‖GafniTao.sharpLandauCoord T sigma R - rho‖) / eta by ring]
    rw [le_div_iff₀ heta]
    simpa using hsep.le
  rw [norm_div, RCLike.norm_natCast]
  change (analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℝ) /
      ‖GafniTao.sharpLandauCoord T sigma R - rho‖ ≤ _
  rw [div_le_iff₀ hnorm]
  calc
    (analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℝ) ≤
        ((7 / (4 * eta)) *
          ‖GafniTao.sharpLandauCoord T sigma R - rho‖) *
            analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) hscale
    _ = ((7 / (4 * eta)) *
          analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho) *
            ‖GafniTao.sharpLandauCoord T sigma R - rho‖ := by ring

theorem norm_sharpLandau_zeroSum_le_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hSigma : 1 - eta ≤ sigma) :
    ‖∑ rho ∈ GafniTao.sharpLandauZeroFinset T hT,
        (analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℂ) /
          (GafniTao.sharpLandauCoord T sigma R - rho)‖ ≤
      (7 / (4 * eta)) * GafniTao.sharpLandauZeroMass T hT := by
  calc
    ‖∑ rho ∈ GafniTao.sharpLandauZeroFinset T hT,
        (analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℂ) /
          (GafniTao.sharpLandauCoord T sigma R - rho)‖ ≤
      ∑ rho ∈ GafniTao.sharpLandauZeroFinset T hT,
        ‖(analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℂ) /
          (GafniTao.sharpLandauCoord T sigma R - rho)‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ GafniTao.sharpLandauZeroFinset T hT,
        (7 / (4 * eta)) *
          analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho := by
      exact Finset.sum_le_sum (fun rho hrho =>
        norm_sharpLandau_zeroTerm_le_of_vK
          hZeroFree hT hHeight heta hWidth hSigma hrho)
    _ = (7 / (4 * eta)) * GafniTao.sharpLandauZeroMass T hT := by
      simp only [GafniTao.sharpLandauZeroMass, Nat.cast_sum]
      rw [Finset.mul_sum]

theorem sharpLandauCoord_not_mem_large_zeros_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hR : R ∈ Set.Icc T (T + 1))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    GafniTao.sharpLandauCoord T sigma R ∉
      GafniTao.SetOfZeros (97 / 100)
        (GafniTao.sharpLandauNormalized T) := by
  intro hz
  have hzNorm : ‖GafniTao.sharpLandauCoord T sigma R‖ ≤ 24 / 25 :=
    (GafniTao.norm_sharpLandauCoord_le hR hSigmaIcc).trans (by norm_num)
  have hzSmall : GafniTao.sharpLandauCoord T sigma R ∈
      GafniTao.sharpLandauZeroFinset T hT := by
    exact (GafniTao.finiteSetOfZeros_mono
      (by norm_num : (24 / 25 : ℝ) < 1)
      (GafniTao.finite_sharpLandauNormalized_zeros hT)).mem_toFinset.mpr
        ⟨hzNorm, hz.2⟩
  have hsep := sharpLandauCoord_zero_separation_of_vK
    hZeroFree hT hHeight heta hWidth hSigma (R := R) hzSmall
  rw [sub_self, norm_zero, mul_zero] at hsep
  linarith

/-- The frozen local partial-fraction estimate with VK horizontal separation
in place of a selected good ordinate. -/
theorem sharpLandau_partialFraction_bound_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hR : R ∈ Set.Icc T (T + 1))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    ‖deriv (GafniTao.sharpLandauNormalized T)
          (GafniTao.sharpLandauCoord T sigma R) /
          GafniTao.sharpLandauNormalized T
            (GafniTao.sharpLandauCoord T sigma R) -
        ∑ rho ∈ GafniTao.sharpLandauZeroFinset T hT,
          analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho /
            (GafniTao.sharpLandauCoord T sigma R - rho)‖ ≤
      GafniTao.sharpLandauPartialFractionConstant *
        Real.log (200 * T ^ (3 : ℝ)) := by
  have hTT : T ∈ Set.Icc (T - 1) (2 * T) := ⟨by linarith, by linarith⟩
  have hB : 1 < 200 * T ^ (3 : ℝ) := by
    have hpow : 1 ≤ T ^ (3 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  unfold GafniTao.sharpLandauPartialFractionConstant
  apply GafniTao.FinalBound (B := 200 * T ^ (3 : ℝ))
      (r' := 19 / 20) (r := 24 / 25) (R' := 97 / 100) (R := 49 / 50)
  · exact hB
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact GafniTao.analyticOnNhd_sharpLandauNormalized hT hTT
  · exact GafniTao.sharpLandauNormalized_zero T
  · exact GafniTao.finite_sharpLandauNormalized_zeros hT
  · intro w hw
    exact GafniTao.norm_sharpLandauNormalized_le hT hTT (by linarith)
  · exact ⟨by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using
        GafniTao.norm_sharpLandauCoord_le hR hSigmaIcc,
      sharpLandauCoord_not_mem_large_zeros_of_vK
        hZeroFree hT hHeight heta hWidth hR hSigmaIcc hSigma⟩

theorem norm_sharpLandauNormalized_logDeriv_le_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hR : R ∈ Set.Icc T (T + 1))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    ‖deriv (GafniTao.sharpLandauNormalized T)
        (GafniTao.sharpLandauCoord T sigma R) /
      GafniTao.sharpLandauNormalized T
        (GafniTao.sharpLandauCoord T sigma R)‖ ≤
      GafniTao.sharpLandauPartialFractionConstant *
          Real.log (200 * T ^ (3 : ℝ)) +
        (7 / (4 * eta)) * GafniTao.sharpLandauZeroMass T hT := by
  let L := deriv (GafniTao.sharpLandauNormalized T)
      (GafniTao.sharpLandauCoord T sigma R) /
    GafniTao.sharpLandauNormalized T
      (GafniTao.sharpLandauCoord T sigma R)
  let Z := ∑ rho ∈ GafniTao.sharpLandauZeroFinset T hT,
    (analyticOrderNatAt (GafniTao.sharpLandauNormalized T) rho : ℂ) /
      (GafniTao.sharpLandauCoord T sigma R - rho)
  have hpartial := sharpLandau_partialFraction_bound_of_vK
    hZeroFree hT hHeight heta hWidth hR hSigmaIcc hSigma
  have hzero := norm_sharpLandau_zeroSum_le_of_vK
    hZeroFree hT hHeight heta hWidth hSigma (R := R)
  change ‖L‖ ≤ _
  calc
    ‖L‖ = ‖(L - Z) + Z‖ := by ring_nf
    _ ≤ ‖L - Z‖ + ‖Z‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hpartial hzero

/-- Positive-height physical `zeta'/zeta` bound at an arbitrary ordinate.
The only distance cost is the reciprocal spare VK width. -/
theorem norm_riemannZeta_logDeriv_positive_height_le_of_vK
    {c H eta T sigma R : ℝ}
    (hZeroFree : GafniTao.VinogradovKorobovRectangleZeroFree c H)
    (hT : 8 ≤ T) (hHeight : H ≤ 3 * T) (heta : 0 < eta)
    (hWidth : 2 * eta ≤
      c / GafniTao.vinogradovKorobovDenominator (3 * T))
    (hR : R ∈ Set.Icc T (T + 1))
    (hSigmaIcc : sigma ∈ Set.Icc (1 / 2) 2)
    (hSigma : 1 - eta ≤ sigma) :
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      (4 / 7 : ℝ) *
        (GafniTao.sharpLandauPartialFractionConstant *
            Real.log (200 * T ^ (3 : ℝ)) +
          (7 / (4 * eta)) * GafniTao.sharpLandauZeroMass T hT) := by
  have hnorm := norm_sharpLandauNormalized_logDeriv_le_of_vK
    hZeroFree hT hHeight heta hWidth hR hSigmaIcc hSigma
  have hcoordNot := sharpLandauCoord_not_mem_large_zeros_of_vK
    hZeroFree hT hHeight heta hWidth hR hSigmaIcc hSigma
  have hzeta : riemannZeta
      (GafniTao.sharpLandauMap T
        (GafniTao.sharpLandauCoord T sigma R)) ≠ 0 := by
    intro hz
    apply hcoordNot
    refine ⟨?_, ?_⟩
    · exact (GafniTao.norm_sharpLandauCoord_le hR hSigmaIcc).trans
        (by norm_num)
    · exact (GafniTao.sharpLandauNormalized_eq_zero_iff T _).2 hz
  have heq := GafniTao.logDeriv_sharpLandauNormalized_eq
    (GafniTao.sharpLandau_physical_point_ne_one hR hT) hzeta
  rw [GafniTao.sharpLandauMap_coord] at heq
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)] at hnorm
  calc
    ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
        riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖ =
      (4 / 7 : ℝ) * ((7 / 4 : ℝ) *
        ‖deriv riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I) /
          riemannZeta ((sigma : ℂ) + (R : ℂ) * Complex.I)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by norm_num)

end

end Tao2026
