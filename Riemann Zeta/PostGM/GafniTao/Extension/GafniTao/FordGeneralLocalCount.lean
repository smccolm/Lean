import GafniTao.FordLocalDetectorGrowthBound

/-!
# A multiplicity-weighted local zero count from general Ford growth

This file eliminates the auxiliary selected-contour height and rearranges the
complete detector inequality into a genuine upper bound for Ford's exact
analytic-multiplicity count `N(t,R)`.
-/

open Complex Finset Filter Set Topology MeasureTheory
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

theorem fordDetectorZetaLogDeriv_center_norm_lt
    {t R : ℝ} (hR : 0 < R) :
    ‖fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t)‖ <
      1 / ((6421 / 10000 : ℝ) * R) := by
  let sigma : ℝ := 1 + (6421 / 10000 : ℝ) * R
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    nlinarith
  have hsigmaNe : (sigma : ℂ) + I * t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [sigma] at hre
    nlinarith
  have hzeta : riemannZeta ((sigma : ℂ) + I * t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  have hEq :
      fordDetectorZetaLogDeriv
          (fordShiftedDetectorCenter sigma t) =
        deriv riemannZeta ((sigma : ℂ) + I * t) /
          riemannZeta ((sigma : ℂ) + I * t) := by
    have hpoint :
        fordShiftedDetectorCenter sigma t = (sigma : ℂ) + I * t := by
      simp [fordShiftedDetectorCenter, mul_comm]
    rw [hpoint, fordDetectorZetaLogDeriv_eq hsigmaNe hzeta,
      logDeriv_apply]
  have hraw := ford_zeta_basic_logDerivative (sigma := sigma) (t := t) hsigma
  rw [hEq]
  rw [← norm_neg]
  simpa [sigma] using hraw

theorem neg_inv_lt_neg_fordDetectorZetaLogDeriv_center_re
    {t R : ℝ} (hR : 0 < R) :
    -(1 / ((6421 / 10000 : ℝ) * R)) <
      -(fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t)).re := by
  have hnorm := fordDetectorZetaLogDeriv_center_norm_lt (t := t) hR
  have hre := Complex.abs_re_le_norm
    (fordDetectorZetaLogDeriv
      (fordShiftedDetectorCenter
        (1 + (6421 / 10000 : ℝ) * R) t))
  have hreUpper :
      (fordDetectorZetaLogDeriv
        (fordShiftedDetectorCenter
          (1 + (6421 / 10000 : ℝ) * R) t)).re <
        1 / ((6421 / 10000 : ℝ) * R) :=
    (le_abs_self _).trans_lt (hre.trans_lt hnorm)
  linarith

set_option maxHeartbeats 1600000 in
/-- Raw local-count consequence of a parameterized Ford growth theorem.
Every surviving term is explicit and the selected contour height has been
eliminated. -/
theorem exists_fordLocalDiskZeroCount_general_raw_bound
    {A B t R : ℝ} (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ht : 3 ≤ t) (hR : 0 < R) (hRUpper : R ≤ 1 / 4) :
    ∀ ε : ℝ, 0 < ε →
      ∃ eta' : ℝ,
        (5 / 2 : ℝ) * R < eta' ∧ eta' < (51 / 20 : ℝ) * R ∧
        (fordLocalDiskZeroCount t R : ℝ) *
            (fordLocalCotUniformLowerConstant / R) <
          1 / ((6421 / 10000 : ℝ) * R) +
          eta' / (Real.pi * t ^ 2) +
          Real.log (1 + 1 / (3 * R)) / (2 * eta') +
          2 * fordGeneralShiftedLeftHighMajorant A B eta'
            (1 + (6421 / 10000 : ℝ) * R) t +
          fordShiftedLeftLowMajorant eta' t
            (eta' - (6421 / 10000 : ℝ) * R) + ε := by
  intro ε hε
  obtain ⟨T0, hT0⟩ :=
    eventually_exists_fordLocalDisk_detector_general_growthBound
      hFord hA hB ht hR hRUpper ε hε
  let T : ℝ := max (max T0 8) (t + 2 * (3 * R) / Real.pi)
  have hT0T : T0 ≤ T :=
    (le_max_left T0 8).trans (le_max_left _ _)
  have h8T : 8 ≤ T :=
    (le_max_right T0 8).trans (le_max_left _ _)
  have hlarge : t + 2 * (3 * R) / Real.pi ≤ T := le_max_right _ _
  obtain ⟨eta', RUpper, RLower, hetaLow, hetaHigh,
      _hRU, _hRL, hdet⟩ := hT0 hT0T h8T hlarge
  have hcentral :=
    neg_inv_lt_neg_fordDetectorZetaLogDeriv_center_re (t := t) hR
  refine ⟨eta', hetaLow, hetaHigh, ?_⟩
  linarith

#print axioms fordDetectorZetaLogDeriv_center_norm_lt
#print axioms exists_fordLocalDiskZeroCount_general_raw_bound

end

end GafniTao
