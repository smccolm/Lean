import GafniTao.FordLogDerivativeTrigonometric
import GafniTao.FordLocalDetectorGrowthBound

/-!
# Height-free forms of the selected Ford detector bounds

The contour height is an internal construction parameter.  These theorems
choose it above the threshold supplied by the selected-contour argument and
retain only the selected radius and the literal analytic majorant.
-/

open Complex Set
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

noncomputable def fordGeneralDetectorMajorant
    (A B eta sigma t : ℝ) : ℝ :=
  eta / (Real.pi * t ^ 2) +
    Real.log (1 + 1 / (sigma + eta - 1)) / (2 * eta) +
    2 * fordGeneralShiftedLeftHighMajorant A B eta sigma t +
    fordShiftedLeftLowMajorant eta t (eta - (sigma - 1))

noncomputable def fordVKDetectorSigma (R : ℝ) : ℝ :=
  1 + (6421 / 10000 : ℝ) * R

noncomputable def fordVKEmptyDetectorMajorant
    (A B eta R t : ℝ) : ℝ :=
  eta / (Real.pi * t ^ 2) +
    Real.log (1 + 1 / (3 * R)) / (2 * eta) +
    2 * fordGeneralShiftedLeftHighMajorant A B eta
      (fordVKDetectorSigma R) t +
    fordShiftedLeftLowMajorant eta t
      (eta - (fordVKDetectorSigma R - 1))

theorem fordRealLogDerivative_eq_neg_detector
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    fordRealLogDerivative sigma t =
      -(fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter sigma t)).re := by
  have hs : 1 < (fordShiftedDetectorCenter sigma t).re := by
    simpa using hsigma
  have hsOne : fordShiftedDetectorCenter sigma t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [fordShiftedDetectorCenter_re, one_re] at this
    linarith
  have hzeta := riemannZeta_ne_zero_of_one_lt_re hs
  rw [fordDetectorZetaLogDeriv_eq hsOne hzeta, logDeriv_apply]
  simp only [fordRealLogDerivative, fordShiftedDetectorCenter, neg_re]
  rw [mul_comm I (t : ℂ)]

private theorem fordChooseContourHeight
    (T0 t etaMax : ℝ) :
    T0 ≤ max (max T0 8) (t + 2 * etaMax / Real.pi) ∧
      8 ≤ max (max T0 8) (t + 2 * etaMax / Real.pi) ∧
      t + 2 * etaMax / Real.pi ≤
        max (max T0 8) (t + 2 * etaMax / Real.pi) := by
  exact ⟨(le_max_left T0 8).trans (le_max_left _ _),
    (le_max_right T0 8).trans (le_max_left _ _), le_max_right _ _⟩

/-- Empty selected-zero form at Ford's standard shifted centre.  It is a
consequence of the full local-disk theorem: the nonpositive zero-count term
is discarded only after the actual multiplicity-weighted count has been
constructed and bounded. -/
theorem exists_fordVK_empty_detector_general_growthBound
    {A B t R : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ eta' : ℝ,
      (5 / 2 : ℝ) * R < eta' ∧ eta' < (51 / 20 : ℝ) * R ∧
      fordRealLogDerivative (fordVKDetectorSigma R) t <
        fordVKEmptyDetectorMajorant A B eta' R t + ε := by
  obtain ⟨T0, hT0⟩ :=
    eventually_exists_fordLocalDisk_detector_general_growthBound
      (t := t) (R := R) hFord hA hB (by linarith) hR hRUpper ε hε
  let T : ℝ := max (max T0 8) (t + 2 * (3 * R) / Real.pi)
  obtain ⟨hT0T, hT8, hTlarge⟩ :=
    fordChooseContourHeight T0 t (3 * R)
  obtain ⟨eta', RUpper, RLower, hetaLow, hetaHigh, _hRU, _hRL, hdet⟩ :=
    hT0 (T := T) hT0T hT8 hTlarge
  have hsigma : 1 < fordVKDetectorSigma R := by
    unfold fordVKDetectorSigma
    nlinarith
  have hEq := fordRealLogDerivative_eq_neg_detector
    (sigma := fordVKDetectorSigma R) (t := t) hsigma
  have hcount : 0 ≤ (fordLocalDiskZeroCount t R : ℝ) := by positivity
  have hkernel : 0 ≤ fordLocalCotUniformLowerConstant / R := by
    exact div_nonneg fordLocalCotUniformLowerConstant_pos.le hR.le
  have hshift : fordVKDetectorSigma R - 1 =
      (6421 / 10000 : ℝ) * R := by
    unfold fordVKDetectorSigma
    ring
  refine ⟨eta', hetaLow, hetaHigh, ?_⟩
  rw [hEq]
  unfold fordVKEmptyDetectorMajorant
  rw [hshift]
  unfold fordVKDetectorSigma
  nlinarith [mul_nonneg hcount hkernel]

/-- One prescribed zero retained at Ford's standard shifted centre. -/
theorem exists_fordVK_singleZero_detector_general_growthBound
    {A B t R : ℝ} {rho : ℂ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 100 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4)
    (hrhoZero : riemannZeta rho = 0)
    (hrhoUpper : rho.re ≤ 1) (hrhoIm : rho.im = t)
    (hrhoNear : 1 - rho.re ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ eta' : ℝ,
      (5 / 2 : ℝ) * R < eta' ∧ eta' < (51 / 20 : ℝ) * R ∧
      fordRealLogDerivative (fordVKDetectorSigma R) t <
        ((analyticVanishingOrder riemannZeta rho : ℂ) *
          fordCotKernel eta'
            (rho - fordShiftedDetectorCenter (fordVKDetectorSigma R) t)).re +
        fordGeneralDetectorMajorant A B eta' (fordVKDetectorSigma R) t + ε := by
  let eta : ℝ := (5 / 2 : ℝ) * R
  let etaMax : ℝ := (51 / 20 : ℝ) * R
  let sigma : ℝ := fordVKDetectorSigma R
  have hsigma : 1 ≤ sigma := by
    dsimp [sigma, fordVKDetectorSigma]
    nlinarith
  have hsigmaStrict : 1 < sigma := by
    dsimp [sigma, fordVKDetectorSigma]
    nlinarith
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaMax : eta < etaMax := by dsimp [eta, etaMax]; nlinarith
  have hPole : sigma - 1 ≤ eta := by
    dsimp [sigma, eta, fordVKDetectorSigma]
    nlinarith
  have hleft : 1 / 2 ≤ sigma - etaMax := by
    dsimp [sigma, etaMax, fordVKDetectorSigma]
    nlinarith
  have hetaUpper : etaMax ≤ Real.pi / 4 := by
    have hpi := Real.pi_gt_three
    dsimp [etaMax]
    nlinarith
  have hrhoNear' : sigma - rho.re ≤ eta := by
    dsimp [sigma, eta, fordVKDetectorSigma]
    nlinarith
  obtain ⟨T0, hT0⟩ :=
    eventually_exists_fordSingleZero_detector_general_growthBound
      hFord hA hB hsigma heta hetaMax hPole hleft hetaUpper
      (by linarith) hrhoZero hrhoUpper hrhoIm hrhoNear' ε hε
  let T : ℝ := max (max T0 8) (t + 2 * etaMax / Real.pi)
  obtain ⟨hT0T, hT8, hTlarge⟩ := fordChooseContourHeight T0 t etaMax
  obtain ⟨eta', RUpper, RLower, hetaLow, hetaHigh, _hRU, _hRL, hdet⟩ :=
    hT0 (T := T) hT0T hT8 hTlarge
  have hEq := fordRealLogDerivative_eq_neg_detector
    (sigma := sigma) (t := t) hsigmaStrict
  refine ⟨eta', ?_, ?_, ?_⟩
  · simpa [eta] using hetaLow
  · simpa [etaMax] using hetaHigh
  · rw [hEq]
    unfold fordGeneralDetectorMajorant
    simpa only [sigma, add_assoc] using hdet

#print axioms exists_fordVK_empty_detector_general_growthBound
#print axioms exists_fordVK_singleZero_detector_general_growthBound

end

end GafniTao
