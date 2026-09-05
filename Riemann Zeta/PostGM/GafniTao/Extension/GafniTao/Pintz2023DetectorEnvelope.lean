import GafniTao.Pintz2023SourceScale
import GafniTao.PintzCutoffBounds

/-!
# Uniform source envelope for Pintz's detector error

The individual zero distance remains a variable.  These lemmas bound every
such error by one expression depending only on the cell endpoint `eta` and
the equation-(4.1) physical scales.
-/

open Filter Asymptotics

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023DetectorExponent
    (eta epsilonX epsilonZeta : ℝ) (k ell : ℕ) : ℝ :=
  2 * (epsilonX / (10 * (ell : ℝ))) * eta +
    (1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta -
      2 * eta / (k : ℝ)

noncomputable def pintz2023DetectorEnvelopeConstant
    (C eta epsilonX epsilonZeta : ℝ) (k ell : ℕ) : ℝ :=
  C * 4 ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) *
    Real.exp (eta ^ 2 / 8) * eta⁻¹ * eta⁻¹ *
    (12 * Real.pi) * (2 / (k : ℝ)) ^ 2 *
    (1 + epsilonX / (10 * (ell : ℝ)))

theorem harmonic_pintz2023SourceX_le
    {T epsilonX : ℝ} {ell : ℕ}
    (hT : Real.exp 1 ≤ T) (hepsilonX : 0 ≤ epsilonX) (hell : 0 < ell) :
    (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) ≤
      (1 + epsilonX / (10 * (ell : ℝ))) * Real.log T := by
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hExpOne : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr zero_lt_one)
  have hTOne : 1 ≤ T := hExpOne.le.trans hT
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 1)) (Set.mem_Ioi.mpr hTPos) hT
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  let a : ℝ := epsilonX / (10 * (ell : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hpow : 0 ≤ T ^ a := (Real.rpow_pos_of_pos hTPos _).le
  have hXle : (pintz2023SourceX T epsilonX ell : ℝ) ≤ T ^ a := by
    simpa only [a] using pintz2023SourceX_cast_le hpow
  have hXpos : 0 < pintz2023SourceX T epsilonX ell := by
    apply pintz2023SourceX_pos
    exact Real.one_le_rpow hTOne ha
  have hlogX : Real.log (pintz2023SourceX T epsilonX ell) ≤
      Real.log (T ^ a) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hXpos))
      (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hTPos _)) hXle
  calc
    (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) ≤
        1 + Real.log (pintz2023SourceX T epsilonX ell) :=
      harmonic_le_one_add_log _
    _ ≤ 1 + Real.log (T ^ a) := by linarith
    _ = 1 + a * Real.log T := by rw [Real.log_rpow hTPos]
    _ ≤ (1 + a) * Real.log T := by nlinarith
    _ = (1 + epsilonX / (10 * (ell : ℝ))) * Real.log T := rfl

theorem pintz2023_sourceX_rpow_le
    {T epsilonX eta etaJ : ℝ} {ell : ℕ}
    (hT : 1 ≤ T) (hepsilonX : 0 ≤ epsilonX) (hell : 0 < ell)
    (hetaJ : 0 ≤ etaJ) (hetaJLe : etaJ ≤ eta) :
    (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) ≤
      T ^ (2 * (epsilonX / (10 * (ell : ℝ))) * eta) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  let a : ℝ := epsilonX / (10 * (ell : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hd : 0 ≤ eta + etaJ := by linarith
  have hXpos : 0 < pintz2023SourceX T epsilonX ell := by
    apply pintz2023SourceX_pos
    exact Real.one_le_rpow hT ha
  have hXle : (pintz2023SourceX T epsilonX ell : ℝ) ≤ T ^ a := by
    simpa only [a] using pintz2023SourceX_cast_le
      (Real.rpow_pos_of_pos hTPos _).le
  calc
    (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) ≤
        (T ^ a) ^ (eta + etaJ) :=
      Real.rpow_le_rpow (by exact_mod_cast hXpos.le) hXle hd
    _ = T ^ (a * (eta + etaJ)) := (Real.rpow_mul hTPos.le _ _).symm
    _ ≤ T ^ (a * (2 * eta)) := by
      apply Real.rpow_le_rpow_of_exponent_le hT
      nlinarith
    _ = T ^ (2 * (epsilonX / (10 * (ell : ℝ))) * eta) := by
      dsimp only [a]
      congr 1
      ring

theorem pintz2023_gamma_factor_le
    {T eta etaJ gamma epsilonZeta : ℝ}
    (hT : 1 ≤ T) (heta : 0 ≤ eta) (hetaJ : 0 ≤ etaJ)
    (hetaJLe : etaJ ≤ eta) (hepsilonZeta : 0 ≤ epsilonZeta)
    (hgamma : |gamma| ≤ T) :
    (|gamma| + 3) ^ ((1 / 2 : ℝ) * (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta) ≤
      4 ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) *
        T ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) := by
  let p : ℝ := (1 / 2 : ℝ) * (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta
  let q : ℝ := (1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta
  have hd : 0 ≤ eta + etaJ := by linarith
  have htwo : 0 ≤ 2 * eta := by positivity
  have hpq : p ≤ q := by
    dsimp only [p, q]
    have hdle : eta + etaJ ≤ 2 * eta := by linarith
    have := Real.rpow_le_rpow hd hdle (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hq : 0 ≤ q := le_trans (by dsimp only [p]; positivity) hpq
  have hbase : |gamma| + 3 ≤ 4 * T := by nlinarith [abs_nonneg gamma]
  have hbaseOne : 1 ≤ 4 * T := by nlinarith
  calc
    (|gamma| + 3) ^ p ≤ (4 * T) ^ p :=
      Real.rpow_le_rpow (by positivity) hbase hp
    _ ≤ (4 * T) ^ q := Real.rpow_le_rpow_of_exponent_le hbaseOne hpq
    _ = 4 ^ q * T ^ q := by
      rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hT)]

theorem pintz2023_lambda_gaussian_factor_le
    {T eta : ℝ} {k : ℕ}
    (hT : 0 < T) (hk : 0 < k)
    (hlambda : 8 ≤ pintz2023SourceLambda T k) :
    Real.exp (eta ^ 2 / pintz2023SourceLambda T k -
        pintz2023SourceLambda T k * eta) *
        (6 * pintz2023SourceLambda T k *
          Real.sqrt (2 * Real.pi * pintz2023SourceLambda T k)) ≤
      Real.exp (eta ^ 2 / 8) * T ^ (-2 * eta / (k : ℝ)) *
        ((12 * Real.pi) * (2 / (k : ℝ)) ^ 2 * Real.log T ^ (2 : ℕ)) := by
  let lambda := pintz2023SourceLambda T k
  have hlambdaPos : 0 < lambda := by dsimp only [lambda]; linarith
  have htwoPiLambda : 1 ≤ 2 * Real.pi * lambda := by
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    dsimp only [lambda]
    nlinarith
  have hsqrt : Real.sqrt (2 * Real.pi * lambda) ≤ 2 * Real.pi * lambda := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hgauss : Real.exp (eta ^ 2 / lambda) ≤ Real.exp (eta ^ 2 / 8) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg eta) (by norm_num) hlambda
  have hexpSplit :
      Real.exp (eta ^ 2 / lambda - lambda * eta) =
        Real.exp (eta ^ 2 / lambda) * Real.exp (-lambda * eta) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkernel : 6 * lambda * Real.sqrt (2 * Real.pi * lambda) ≤
      12 * Real.pi * lambda ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 6 * lambda)]
  have hlambdaSq : lambda ^ 2 =
      (2 / (k : ℝ)) ^ 2 * Real.log T ^ (2 : ℕ) := by
    dsimp only [lambda, pintz2023SourceLambda]
    ring
  change Real.exp (eta ^ 2 / lambda - lambda * eta) *
      (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) ≤ _
  rw [hexpSplit, exp_neg_pintz2023SourceLambda_mul hT hk]
  calc
    Real.exp (eta ^ 2 / lambda) * T ^ (-2 * eta / (k : ℝ)) *
          (6 * lambda * Real.sqrt (2 * Real.pi * lambda)) ≤
        Real.exp (eta ^ 2 / 8) * T ^ (-2 * eta / (k : ℝ)) *
          (12 * Real.pi * lambda ^ 2) := by
      gcongr
    _ = Real.exp (eta ^ 2 / 8) * T ^ (-2 * eta / (k : ℝ)) *
        ((12 * Real.pi) * (2 / (k : ℝ)) ^ 2 * Real.log T ^ (2 : ℕ)) := by
      rw [hlambdaSq]
      ring

/-- Every zero in the cell `0 < etaJ ≤ eta` satisfies the same decaying
source envelope.  This is the quantitative form of Pintz (4.8)--(4.11)
before the eventual power saving is invoked. -/
theorem pintz2023_left_scale_le_detector_envelope
    {C T eta etaJ gamma epsilonX epsilonZeta : ℝ} {k ell : ℕ}
    (hC : 0 ≤ C) (hT : Real.exp 1 ≤ T)
    (hepsilonX : 0 < epsilonX) (hepsilonZeta : 0 < epsilonZeta)
    (hk : 0 < k) (hell : 0 < ell)
    (heta : 0 < eta) (hetaJ : 0 < etaJ) (hetaJLe : etaJ ≤ eta)
    (hlambda : 8 ≤ pintz2023SourceLambda T k)
    (hgamma : |gamma| ≤ T) :
    C * (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) *
        (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) *
        eta⁻¹ * (eta + etaJ)⁻¹ *
        (|gamma| + 3) ^ ((1 / 2 : ℝ) *
          (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta) *
        Real.exp (eta ^ 2 / pintz2023SourceLambda T k -
          pintz2023SourceLambda T k * eta) *
        (6 * pintz2023SourceLambda T k *
          Real.sqrt (2 * Real.pi * pintz2023SourceLambda T k)) ≤
      pintz2023DetectorEnvelopeConstant C eta epsilonX epsilonZeta k ell *
        Real.log T ^ (3 : ℕ) *
        T ^ pintz2023DetectorExponent eta epsilonX epsilonZeta k ell := by
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hTStrict : 1 < T := by
    have : 1 < Real.exp 1 := by
      simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr zero_lt_one)
    exact this.trans_le hT
  have hTOne : 1 ≤ T := hTStrict.le
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have hSourceXPos : 0 < pintz2023SourceX T epsilonX ell := by
    apply pintz2023SourceX_pos
    exact Real.one_le_rpow hTOne (by positivity)
  have hHNonneg :
      0 ≤ (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) := by
    exact_mod_cast (harmonic_pos hSourceXPos.ne').le
  have hlogPos : 0 < Real.log T := Real.log_pos hTStrict
  have hX := pintz2023_sourceX_rpow_le hTOne hepsilonX.le hell
    hetaJ.le hetaJLe
  have hH := harmonic_pintz2023SourceX_le hT hepsilonX.le hell
  have hInv : (eta + etaJ)⁻¹ ≤ eta⁻¹ := by
    exact (inv_le_inv₀ (by linarith) heta).2 (by linarith)
  have hGamma := pintz2023_gamma_factor_le hTOne heta.le hetaJ.le
    hetaJLe hepsilonZeta.le hgamma
  have hLambda := pintz2023_lambda_gaussian_factor_le
    (eta := eta) hTPos hk hlambda
  let xexp : ℝ := 2 * (epsilonX / (10 * (ell : ℝ))) * eta
  let q : ℝ := (1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta
  let nexp : ℝ := -2 * eta / (k : ℝ)
  have hPreOne : 0 ≤ C * T ^ xexp *
      ((1 + epsilonX / (10 * (ell : ℝ))) * Real.log T) * eta⁻¹ := by
    dsimp only [xexp]
    positivity
  have hPreTwo : 0 ≤ C * T ^ xexp *
      ((1 + epsilonX / (10 * (ell : ℝ))) * Real.log T) * eta⁻¹ * eta⁻¹ := by
    positivity
  have hPreThree : 0 ≤ C * T ^ xexp *
      ((1 + epsilonX / (10 * (ell : ℝ))) * Real.log T) * eta⁻¹ * eta⁻¹ *
      (4 ^ q * T ^ q) := by
    positivity
  have hpow : T ^ xexp * T ^ q * T ^ nexp =
      T ^ (xexp + q + nexp) := by
    rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos]
  have hGrouped :
      C * (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) *
          (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) *
          eta⁻¹ * (eta + etaJ)⁻¹ *
          (|gamma| + 3) ^ ((1 / 2 : ℝ) *
            (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta) *
          Real.exp (eta ^ 2 / pintz2023SourceLambda T k -
            pintz2023SourceLambda T k * eta) *
          (6 * pintz2023SourceLambda T k *
            Real.sqrt (2 * Real.pi * pintz2023SourceLambda T k)) =
        C * (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) *
          (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) *
          eta⁻¹ * (eta + etaJ)⁻¹ *
          (|gamma| + 3) ^ ((1 / 2 : ℝ) *
            (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta) *
          (Real.exp (eta ^ 2 / pintz2023SourceLambda T k -
            pintz2023SourceLambda T k * eta) *
          (6 * pintz2023SourceLambda T k *
            Real.sqrt (2 * Real.pi * pintz2023SourceLambda T k))) := by ring
  rw [hGrouped]
  calc
    C * (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) *
          (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) *
          eta⁻¹ * (eta + etaJ)⁻¹ *
          (|gamma| + 3) ^ ((1 / 2 : ℝ) *
            (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta) *
          (Real.exp (eta ^ 2 / pintz2023SourceLambda T k -
            pintz2023SourceLambda T k * eta) *
          (6 * pintz2023SourceLambda T k *
            Real.sqrt (2 * Real.pi * pintz2023SourceLambda T k))) ≤
        C * T ^ xexp *
          ((1 + epsilonX / (10 * (ell : ℝ))) * Real.log T) *
          eta⁻¹ * eta⁻¹ *
          (4 ^ q * T ^ q) *
          (Real.exp (eta ^ 2 / 8) * T ^ nexp *
            ((12 * Real.pi) * (2 / (k : ℝ)) ^ 2 *
              Real.log T ^ (2 : ℕ))) := by
      dsimp only [xexp, q, nexp]
      gcongr
    _ = pintz2023DetectorEnvelopeConstant C eta epsilonX epsilonZeta k ell *
          Real.log T ^ (3 : ℕ) *
          T ^ pintz2023DetectorExponent eta epsilonX epsilonZeta k ell := by
      dsimp only [pintz2023DetectorEnvelopeConstant,
        pintz2023DetectorExponent, xexp, q, nexp]
      calc
        C * T ^ (2 * (epsilonX / (10 * (ell : ℝ))) * eta) *
              ((1 + epsilonX / (10 * (ell : ℝ))) * Real.log T) *
              eta⁻¹ * eta⁻¹ *
              (4 ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) *
                T ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta)) *
              (Real.exp (eta ^ 2 / 8) * T ^ (-2 * eta / (k : ℝ)) *
                ((12 * Real.pi) * (2 / (k : ℝ)) ^ 2 *
                  Real.log T ^ (2 : ℕ))) =
            (C * 4 ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) *
              Real.exp (eta ^ 2 / 8) * eta⁻¹ * eta⁻¹ *
              (12 * Real.pi) * (2 / (k : ℝ)) ^ 2 *
              (1 + epsilonX / (10 * (ell : ℝ)))) *
              (Real.log T * Real.log T ^ (2 : ℕ)) *
              (T ^ (2 * (epsilonX / (10 * (ell : ℝ))) * eta) *
                T ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) *
                T ^ (-2 * eta / (k : ℝ))) := by ring
        _ = (C * 4 ^ ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) *
              Real.exp (eta ^ 2 / 8) * eta⁻¹ * eta⁻¹ *
              (12 * Real.pi) * (2 / (k : ℝ)) ^ 2 *
              (1 + epsilonX / (10 * (ell : ℝ)))) *
              Real.log T ^ (3 : ℕ) *
              T ^ (2 * (epsilonX / (10 * (ell : ℝ))) * eta +
                ((1 / 2 : ℝ) * (2 * eta) ^ (3 / 2 : ℝ) + epsilonZeta) +
                (-2 * eta / (k : ℝ))) := by
          rw [hpow]
          ring
        _ = _ := by congr 3 <;> ring

#print axioms harmonic_pintz2023SourceX_le
#print axioms pintz2023_sourceX_rpow_le
#print axioms pintz2023_gamma_factor_le
#print axioms pintz2023_lambda_gaussian_factor_le
#print axioms pintz2023_left_scale_le_detector_envelope

end

end GafniTao
