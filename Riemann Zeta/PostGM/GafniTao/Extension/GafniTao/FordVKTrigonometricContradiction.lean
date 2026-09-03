import GafniTao.FordVKMajorant

/-!
# Ford's five-frequency contradiction at the VK scale
-/

namespace GafniTao

noncomputable section

def fordVKA1 : ℝ := 9 / 40
def fordVKA2 : ℝ := 9 / 10

noncomputable def fordVKAuxiliaryTrigCoefficient : ℝ :=
  fordTrigB2 fordVKA1 fordVKA2 +
    fordTrigB3 fordVKA1 fordVKA2 + fordTrigB4

noncomputable def fordVKTrigGap : ℝ :=
  fordTrigB1 fordVKA1 fordVKA2 / 3 -
    fordTrigB0 fordVKA1 fordVKA2 / 2

/-- The scale facts used at each of the four positive frequencies. -/
def FordVKScaleData (t : ℝ) : Prop :=
  Real.exp (Real.exp 1) ≤ t ∧
    9 ≤ fordVKLogLog t ∧ fordVKRadius t ≤ 1 / 8

theorem fordVK_trig_coefficients_nonneg :
    0 ≤ fordTrigB0 fordVKA1 fordVKA2 ∧
    0 ≤ fordTrigB1 fordVKA1 fordVKA2 ∧
    0 ≤ fordTrigB2 fordVKA1 fordVKA2 ∧
    0 ≤ fordTrigB3 fordVKA1 fordVKA2 ∧
    0 ≤ fordTrigB4 := by
  norm_num [fordVKA1, fordVKA2, fordTrigB0, fordTrigB1,
    fordTrigB2, fordTrigB3, fordTrigB4]

theorem fordVKTrigGap_pos : 0 < fordVKTrigGap := by
  norm_num [fordVKTrigGap, fordVKA1, fordVKA2, fordTrigB0,
    fordTrigB1, fordTrigB2, fordTrigB3, fordTrigB4]

private theorem fordVK_correction_bound
    {D R u eta x c : ℝ}
    (hD : 0 < D) (hR : 0 < R) (hu : 9 ≤ u)
    (hDR : D * R = u) (heta : R < eta)
    (hx : 0 ≤ x) (hxc : x ≤ 3 * c / D) (hc : 0 < c) :
    x / eta ^ 2 ≤ (1 / 27 : ℝ) * c * D := by
  have hsq : R ^ 2 ≤ eta ^ 2 := by nlinarith
  have hstep1 : x / eta ^ 2 ≤ x / R ^ 2 := by
    exact div_le_div_of_nonneg_left hx (sq_pos_of_pos hR) hsq
  have hstep2 : x / R ^ 2 ≤ (3 * c / D) / R ^ 2 :=
    div_le_div_of_nonneg_right hxc (sq_pos_of_pos hR).le
  have heq : (3 * c / D) / R ^ 2 = 3 * c / u ^ 2 * D := by
    field_simp [hD.ne', hR.ne'] at hDR ⊢
    nlinarith
  have huSq : (81 : ℝ) ≤ u ^ 2 := by nlinarith
  have hstep3 : 3 * c / u ^ 2 * D ≤ (1 / 27 : ℝ) * c * D := by
    have hdiv : 3 * c / u ^ 2 ≤ 3 * c / 81 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) huSq
    nlinarith
  exact hstep1.trans (hstep2.trans (heq.trans_le hstep3))

private theorem fordVK_reciprocal_target_bound
    {D x c : ℝ} (hD : 0 < D) (hx : 0 < x) (hc : 0 < c)
    (hxc : x ≤ 3 * c / D) :
    -(1 / x) ≤ -(D / (3 * c)) := by
  have hinv : 1 / (3 * c / D) ≤ 1 / x :=
    one_div_le_one_div_of_le hx hxc
  have heq : 1 / (3 * c / D) = D / (3 * c) := by
    field_simp [hD.ne', hc.ne']
  linarith

private theorem fordVK_empty_frequency_bound
    {A B c t q : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hcGeom : c ≤ 1 / 2)
    (ht : 100 ≤ t) (hscale : FordVKScaleData t)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4)
    (hscaleq : FordVKScaleData (q * t)) :
    fordRealLogDerivative
        (1 + 2 * c / vinogradovKorobovDenominator t) (q * t) <
      4 * (fordVKMajorantCoefficient A B + 1) *
        vinogradovKorobovDenominator t := by
  let D : ℝ := vinogradovKorobovDenominator t
  let Dq : ℝ := vinogradovKorobovDenominator (q * t)
  let Rq : ℝ := fordVKRadius (q * t)
  let lambda : ℝ := 2 * c / D
  let sigma : ℝ := 1 + lambda
  obtain ⟨hbase, hu, _hR⟩ := hscale
  obtain ⟨hbaseq, huq, hRqUpper⟩ := hscaleq
  have hqPos : 0 < q := zero_lt_one.trans_le hqOne
  have htPos : 0 < t := by linarith
  have htq : 100 ≤ q * t := by nlinarith
  have hD : 0 < D := vinogradovKorobovDenominator_pos hbase
  have hDq : 0 < Dq := vinogradovKorobovDenominator_pos hbaseq
  have hRq : 0 < Rq := fordVKRadius_pos (q * t)
  have hDqUpper : Dq ≤ 4 * D := by
    dsimp [Dq, D]
    exact vinogradovKorobovDenominator_mul_le_four ht hu hqOne hqFour
  have hDqRq : Dq * Rq = fordVKLogLog (q * t) := by
    dsimp [Dq, Rq]
    rw [mul_comm, fordVKRadius_mul_denominator hbaseq]
  have hDRqLower : 9 ≤ 4 * D * Rq := by
    have hm := mul_le_mul_of_nonneg_right hDqUpper hRq.le
    rw [hDqRq] at hm
    linarith
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hlambdaRq : lambda ≤ Rq / 2 := by
    dsimp [lambda]
    apply (div_le_iff₀ hD).mpr
    nlinarith
  let eta0 : ℝ := (5 / 2 : ℝ) * Rq
  let etaMax : ℝ := (51 / 20 : ℝ) * Rq
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  have hetaRange : eta0 < etaMax := by dsimp [eta0, etaMax]; nlinarith
  have hPole : sigma - 1 ≤ eta0 := by
    dsimp [sigma, eta0]
    nlinarith
  have hleft : 1 / 2 ≤ sigma - etaMax := by
    dsimp [sigma, etaMax]
    nlinarith
  have hetaMaxPi : etaMax ≤ Real.pi / 4 := by
    have hpi := Real.pi_gt_three
    dsimp [etaMax]
    nlinarith
  obtain ⟨eta, hetaLow, hetaHigh, hdet⟩ :=
    exists_fordEmpty_detector_general_growthBound
      (t := q * t) hFord hA hB (by dsimp [sigma]; linarith) heta0 hetaRange
      hPole hleft hetaMaxPi (by linarith [htq]) hDq
  have hmajor :=
    fordGeneralDetectorMajorant_le_vinogradovKorobovDenominator
      hA hB htq rfl hbaseq (by linarith)
      (hRqUpper.trans (by norm_num))
      (by simpa [eta0, Rq] using hetaLow)
      (by simpa [etaMax, Rq] using hetaHigh)
      hlambda.le hlambdaRq
  have hcoef : 0 ≤ fordVKMajorantCoefficient A B + 1 := by
    have := fordVKMajorantCoefficient_pos hA hB
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hDqUpper hcoef
  dsimp [Dq, D] at hscaled
  dsimp [sigma, lambda, D] at hdet hmajor ⊢
  nlinarith

set_option maxHeartbeats 2400000 in
/-- If a zero entered the proposed strip, the exact five-frequency Euler
inequality and four contour bounds would contradict one another. -/
theorem fordVK_no_positive_height_zero
    {A B c t : ℝ} {rho : ℂ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hcGeom : c ≤ 1 / 2)
    (hcDom :
      fordTrigB1 fordVKA1 fordVKA2 *
          (fordVKMajorantCoefficient A B + 1 + (1 / 27 : ℝ) * c) +
        4 * fordVKAuxiliaryTrigCoefficient *
          (fordVKMajorantCoefficient A B + 1) < fordVKTrigGap / c)
    (ht : 100 ≤ t)
    (hscale : FordVKScaleData t)
    (hscale2 : FordVKScaleData (2 * t))
    (hscale3 : FordVKScaleData (3 * t))
    (hscale4 : FordVKScaleData (4 * t))
    (hrhoZero : riemannZeta rho = 0)
    (hrhoIm : rho.im = t)
    (hrhoNear : 1 - c / vinogradovKorobovDenominator t ≤ rho.re) :
    False := by
  let D : ℝ := vinogradovKorobovDenominator t
  let R : ℝ := fordVKRadius t
  let delta : ℝ := 1 - rho.re
  let lambda : ℝ := 2 * c / D
  let sigma : ℝ := 1 + lambda
  obtain ⟨hbase, hu, hRUpper⟩ := hscale
  have hD : 0 < D := vinogradovKorobovDenominator_pos hbase
  have hR : 0 < R := fordVKRadius_pos t
  have hDR : D * R = fordVKLogLog t := by
    dsimp [D, R]
    rw [mul_comm, fordVKRadius_mul_denominator hbase]
  have hrhoUpper : rho.re ≤ 1 := by
    by_contra h
    exact (riemannZeta_ne_zero_of_one_lt_re (lt_of_not_ge h)) hrhoZero
  have hdelta : 0 ≤ delta := by dsimp [delta]; linarith
  have hdeltaUpper : delta ≤ c / D := by
    dsimp [delta, D] at hrhoNear ⊢
    linarith
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hlambdaR : lambda ≤ R / 2 := by
    dsimp [lambda]
    apply (div_le_iff₀ hD).mpr
    rw [show R / 2 * D = fordVKLogLog t / 2 by
      calc
        R / 2 * D = (D * R) / 2 := by ring
        _ = fordVKLogLog t / 2 := by rw [hDR]]
    nlinarith
  have hxPos : 0 < sigma - rho.re := by
    dsimp [sigma, lambda, delta]
    linarith
  have hxUpper : sigma - rho.re ≤ 3 * c / D := by
    calc
      sigma - rho.re = lambda + delta := by dsimp [sigma, delta]; ring
      _ ≤ 2 * c / D + c / D := by
        dsimp [lambda]
        simpa [add_comm] using add_le_add_right hdeltaUpper (2 * c / D)
      _ = 3 * c / D := by ring
  let eta0 : ℝ := (5 / 2 : ℝ) * R
  let etaMax : ℝ := (51 / 20 : ℝ) * R
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  have hetaRange : eta0 < etaMax := by dsimp [eta0, etaMax]; nlinarith
  have hPole : sigma - 1 ≤ eta0 := by
    dsimp [sigma, eta0]
    nlinarith
  have hleft : 1 / 2 ≤ sigma - etaMax := by
    dsimp [sigma, etaMax]
    nlinarith
  have hetaMaxPi : etaMax ≤ Real.pi / 4 := by
    have hpi := Real.pi_gt_three
    dsimp [etaMax]
    nlinarith
  have hrhoNearEta : sigma - rho.re ≤ eta0 := by
    apply hxUpper.trans
    dsimp [eta0]
    apply (div_le_iff₀ hD).mpr
    have hmul : (5 / 2 : ℝ) * R * D =
        (5 / 2) * fordVKLogLog t := by
      rw [mul_assoc, mul_comm R D, hDR]
    rw [hmul]
    nlinarith
  obtain ⟨eta, hetaLow, hetaHigh, hdet⟩ :=
    exists_fordSingleZero_detector_general_growthBound
      hFord hA hB (by dsimp [sigma]; linarith) heta0 hetaRange
      hPole hleft hetaMaxPi (by linarith) hrhoZero hrhoUpper hrhoIm
      hrhoNearEta hD
  have hetaR : R < eta := by
    dsimp [eta0] at hetaLow
    nlinarith
  have hcot := fordSingleZero_cotangentContribution_le
    (eta := eta) (sigma := sigma) (t := t) (heta0.trans hetaLow)
      (by linarith) hrhoZero hrhoUpper hrhoIm hxPos
      (hrhoNearEta.trans_lt hetaLow)
  have hmajor :=
    fordGeneralDetectorMajorant_le_vinogradovKorobovDenominator
      hA hB ht rfl hbase (by linarith)
      (hRUpper.trans (by norm_num))
      (by simpa [eta0, R] using hetaLow)
      (by simpa [etaMax, R] using hetaHigh)
      hlambda.le hlambdaR
  have hcorr := fordVK_correction_bound hD hR hu hDR hetaR hxPos.le
    hxUpper hc
  have hrecip := fordVK_reciprocal_target_bound hD hxPos hc hxUpper
  have hD1 : fordRealLogDerivative sigma t <
      -(D / (3 * c)) +
        ((1 / 27 : ℝ) * c + fordVKMajorantCoefficient A B + 1) * D := by
    apply hdet.trans_le
    calc
      ((RiemannZeta.GuthMaynard.analyticVanishingOrder riemannZeta rho : ℂ) *
            fordCotKernel eta
              (rho - fordShiftedDetectorCenter sigma t)).re +
          fordGeneralDetectorMajorant A B eta sigma t + D ≤
        (-(1 / (sigma - rho.re)) + (sigma - rho.re) / eta ^ 2) +
          fordVKMajorantCoefficient A B * D + D := by gcongr
      _ ≤ -(D / (3 * c)) +
          ((1 / 27 : ℝ) * c + fordVKMajorantCoefficient A B + 1) * D := by
            dsimp [D] at hrecip hcorr ⊢
            nlinarith
  have hsigma : 1 < sigma := by dsimp [sigma]; linarith
  have hD0 := fordRealLogDerivative_zero_lt_inv hsigma
  have hInv : 1 / (sigma - 1) = D / (2 * c) := by
    have hs : sigma - 1 = lambda := by dsimp [sigma]; ring
    rw [hs]
    dsimp [lambda]
    field_simp [hD.ne', hc.ne']
  rw [hInv] at hD0
  have hD2 := fordVK_empty_frequency_bound hFord hA hB hc hcGeom ht
    ⟨hbase, hu, hRUpper⟩ (by norm_num) (by norm_num) hscale2
  have hD3 := fordVK_empty_frequency_bound hFord hA hB hc hcGeom ht
    ⟨hbase, hu, hRUpper⟩ (by norm_num) (by norm_num) hscale3
  have hD4 := fordVK_empty_frequency_bound hFord hA hB hc hcGeom ht
    ⟨hbase, hu, hRUpper⟩ (by norm_num) (by norm_num) hscale4
  change fordRealLogDerivative sigma (2 * t) <
    4 * (fordVKMajorantCoefficient A B + 1) * D at hD2
  change fordRealLogDerivative sigma (3 * t) <
    4 * (fordVKMajorantCoefficient A B + 1) * D at hD3
  change fordRealLogDerivative sigma (4 * t) <
    4 * (fordVKMajorantCoefficient A B + 1) * D at hD4
  have htrig := ford_logDerivative_trigonometric_nonneg hsigma
    fordVKA1 fordVKA2 t
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := fordVK_trig_coefficients_nonneg
  have hb1pos : 0 < fordTrigB1 fordVKA1 fordVKA2 := by
    norm_num [fordVKA1, fordVKA2, fordTrigB1]
  have h0mul := mul_le_mul_of_nonneg_left hD0.le hb0
  have h1mul := mul_lt_mul_of_pos_left hD1 hb1pos
  have h2mul := mul_le_mul_of_nonneg_left hD2.le hb2
  have h3mul := mul_le_mul_of_nonneg_left hD3.le hb3
  have h4mul := mul_le_mul_of_nonneg_left hD4.le hb4
  have hupper :
      fordTrigB0 fordVKA1 fordVKA2 * fordRealLogDerivative sigma 0 +
        fordTrigB1 fordVKA1 fordVKA2 * fordRealLogDerivative sigma t +
        fordTrigB2 fordVKA1 fordVKA2 * fordRealLogDerivative sigma (2 * t) +
        fordTrigB3 fordVKA1 fordVKA2 * fordRealLogDerivative sigma (3 * t) +
        fordTrigB4 * fordRealLogDerivative sigma (4 * t) <
      fordTrigB0 fordVKA1 fordVKA2 * (D / (2 * c)) +
        fordTrigB1 fordVKA1 fordVKA2 *
          (-(D / (3 * c)) +
            ((1 / 27 : ℝ) * c + fordVKMajorantCoefficient A B + 1) * D) +
        fordVKAuxiliaryTrigCoefficient *
          (4 * (fordVKMajorantCoefficient A B + 1) * D) := by
    unfold fordVKAuxiliaryTrigCoefficient
    nlinarith
  have hnegative :
      fordTrigB0 fordVKA1 fordVKA2 * (D / (2 * c)) +
        fordTrigB1 fordVKA1 fordVKA2 *
          (-(D / (3 * c)) +
            ((1 / 27 : ℝ) * c + fordVKMajorantCoefficient A B + 1) * D) +
        fordVKAuxiliaryTrigCoefficient *
          (4 * (fordVKMajorantCoefficient A B + 1) * D) < 0 := by
    have hdomScaled := mul_lt_mul_of_pos_right hcDom (mul_pos hc hD)
    rw [show fordVKTrigGap =
      fordTrigB1 fordVKA1 fordVKA2 / 3 -
        fordTrigB0 fordVKA1 fordVKA2 / 2 by rfl] at hdomScaled
    field_simp [hc.ne'] at hdomScaled ⊢
    nlinarith
  linarith

#print axioms fordVKTrigGap_pos
#print axioms fordVK_no_positive_height_zero

end

end GafniTao
