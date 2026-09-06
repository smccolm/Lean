import GafniTao.Pintz2023DetectorEnvelope

/-!
# Eventual discharge of Pintz's detector errors

Strict negativity of the source exponent is converted here into the literal
`1/8` bounds required by the contour detector.  The logarithmic factors are
absorbed by an explicit little-oh argument.
-/

open Filter Asymptotics

namespace GafniTao

noncomputable section

theorem eventually_const_mul_log_rpow_mul_negative_rpow_le
    {C p q b : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hb : 0 < b) :
    ∀ᶠ T : ℝ in atTop,
      C * Real.log T ^ p * T ^ (-q) ≤ b := by
  have hLittle :=
    (isLittleO_log_rpow_rpow_atTop p hq).const_mul_left (C / b)
  filter_upwards [hLittle.eventuallyLE,
    eventually_ge_atTop (Real.exp 1)] with T hbound hT
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogNonneg : 0 ≤ Real.log T := by
    have hExpOne : 1 ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_lt_exp.mpr zero_lt_one).le
    exact Real.log_nonneg (hExpOne.trans hT)
  have hleftNonneg : 0 ≤ (C / b) * Real.log T ^ p := by positivity
  have hrightNonneg : 0 ≤ T ^ q := (Real.rpow_pos_of_pos hTPos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hleftNonneg,
    Real.norm_eq_abs, abs_of_nonneg hrightNonneg] at hbound
  have hcancel : T ^ q * T ^ (-q) = 1 := by
    rw [← Real.rpow_add hTPos]
    norm_num
  calc
    C * Real.log T ^ p * T ^ (-q) =
        b * ((C / b) * Real.log T ^ p) * T ^ (-q) := by
      field_simp [hb.ne']
    _ ≤ b * T ^ q * T ^ (-q) := by gcongr
    _ = b * (T ^ q * T ^ (-q)) := by ring
    _ = b := by rw [hcancel, mul_one]

theorem eventually_pintz2023_detector_envelope_le_eighth
    {C eta epsilonX epsilonZeta : ℝ} {k ell : ℕ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hepsilonX : 0 < epsilonX) (hk : 0 < k) (hell : 0 < ell)
    (hdecay : pintz2023DetectorExponent eta epsilonX epsilonZeta k ell < 0) :
    ∀ᶠ T : ℝ in atTop,
      pintz2023DetectorEnvelopeConstant C eta epsilonX epsilonZeta k ell *
        Real.log T ^ (3 : ℕ) *
        T ^ pintz2023DetectorExponent eta epsilonX epsilonZeta k ell ≤ 1 / 8 := by
  have hConstant : 0 ≤
      pintz2023DetectorEnvelopeConstant C eta epsilonX epsilonZeta k ell := by
    unfold pintz2023DetectorEnvelopeConstant
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have h := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (p := 3) hConstant (neg_pos.mpr hdecay)
      (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [h] with T hT
  rw [← Real.rpow_natCast (Real.log T) 3]
  simpa only [neg_neg] using hT

theorem eventually_pintz2023_left_scale_le_eighth
    {C eta epsilonX epsilonZeta : ℝ} {k ell : ℕ}
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hepsilonX : 0 < epsilonX) (hepsilonZeta : 0 < epsilonZeta)
    (hk : 0 < k) (hell : 0 < ell)
    (hdecay : pintz2023DetectorExponent eta epsilonX epsilonZeta k ell < 0) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp 1 ≤ T ∧ 8 ≤ pintz2023SourceLambda T k ∧
      ∀ etaJ gamma : ℝ,
        0 < etaJ → etaJ ≤ eta → |gamma| ≤ T →
        C * (pintz2023SourceX T epsilonX ell : ℝ) ^ (eta + etaJ) *
            (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) *
            eta⁻¹ * (eta + etaJ)⁻¹ *
            (|gamma| + 3) ^ ((1 / 2 : ℝ) *
              (eta + etaJ) ^ (3 / 2 : ℝ) + epsilonZeta) *
            Real.exp (eta ^ 2 / pintz2023SourceLambda T k -
              pintz2023SourceLambda T k * eta) *
            (6 * pintz2023SourceLambda T k *
              Real.sqrt (2 * Real.pi * pintz2023SourceLambda T k)) ≤ 1 / 8 := by
  have hEnvelope := eventually_pintz2023_detector_envelope_le_eighth
    hC heta hepsilonX hk hell hdecay
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact (Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal))
  filter_upwards [hEnvelope, eventually_ge_atTop (Real.exp 1),
    hLambda.eventually (eventually_ge_atTop 8)] with T hEnv hT hLam
  refine ⟨hT, hLam, ?_⟩
  intro etaJ gamma hetaJ hetaJLe hgamma
  exact (pintz2023_left_scale_le_detector_envelope hC hT
    hepsilonX hepsilonZeta hk hell heta hetaJ hetaJLe hLam hgamma).trans hEnv

theorem pintz2023_pole_scale_le_source_envelope
    {T eta gamma epsilonX : ℝ} {k ell : ℕ}
    (hT : Real.exp 1 ≤ T) (hepsilonX : 0 ≤ epsilonX)
    (hk : 0 < k) (hell : 0 < ell)
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 24)
    (hlambda : 8 ≤ pintz2023SourceLambda T k)
    (hgammaOne : 1 ≤ |gamma|)
    (hgammaLambda : 2 * pintz2023SourceLambda T k ≤ |gamma|) :
    (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) * |gamma|⁻¹ *
        Real.exp (eta ^ 2 / pintz2023SourceLambda T k +
          pintz2023SourceLambda T k * eta -
          gamma ^ 2 / pintz2023SourceLambda T k) ≤
      ((1 + epsilonX / (10 * (ell : ℝ))) * Real.exp (eta ^ 2 / 8)) *
        Real.log T * T ^ (-6 / (k : ℝ)) := by
  let lambda := pintz2023SourceLambda T k
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlambdaPos : 0 < lambda := by dsimp only [lambda]; linarith
  have hH := harmonic_pintz2023SourceX_le hT hepsilonX hell
  have hinv : |gamma|⁻¹ ≤ 1 := by
    simpa only [inv_one] using
      ((inv_le_inv₀ (by positivity : 0 < |gamma|) zero_lt_one).2 hgammaOne)
  have hgammaSq : (2 * lambda) ^ 2 ≤ gamma ^ 2 := by
    calc
      (2 * lambda) ^ 2 ≤ |gamma| ^ 2 :=
        (sq_le_sq₀ (show (0 : ℝ) ≤ 2 * lambda by positivity)
          (abs_nonneg gamma)).2 hgammaLambda
      _ = gamma ^ 2 := sq_abs gamma
  have hetaDiv : eta ^ 2 / lambda ≤ eta ^ 2 / 8 :=
    div_le_div_of_nonneg_left (sq_nonneg eta) (by norm_num) hlambda
  have hexponent : eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda ≤
      eta ^ 2 / 8 - 3 * lambda := by
    have hgammaDiv : 4 * lambda ≤ gamma ^ 2 / lambda := by
      apply (le_div_iff₀ hlambdaPos).2
      nlinarith
    nlinarith
  have hexp : Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) ≤
      Real.exp (eta ^ 2 / 8) * T ^ (-6 / (k : ℝ)) := by
    calc
      Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) ≤
          Real.exp (eta ^ 2 / 8 - 3 * lambda) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (eta ^ 2 / 8) * Real.exp (-3 * lambda) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by
        rw [show lambda = pintz2023SourceLambda T k by rfl,
          exp_neg_three_pintz2023SourceLambda hTPos hk]
  change (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) * |gamma|⁻¹ *
      Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) ≤ _
  have hTOne : 1 ≤ T := by
    have hExpOne : 1 ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_lt_exp.mpr zero_lt_one).le
    exact hExpOne.trans hT
  have hlogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have hHUpperNonneg :
      0 ≤ (1 + epsilonX / (10 * (ell : ℝ))) * Real.log T := by
    positivity
  calc
    (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) * |gamma|⁻¹ *
        Real.exp (eta ^ 2 / lambda + lambda * eta - gamma ^ 2 / lambda) ≤
      ((1 + epsilonX / (10 * (ell : ℝ))) * Real.log T) * 1 *
        (Real.exp (eta ^ 2 / 8) * T ^ (-6 / (k : ℝ))) := by
      gcongr
    _ = _ := by ring

theorem eventually_pintz2023_pole_scale_le_eighth
    {eta epsilonX : ℝ} {k ell : ℕ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 24)
    (hepsilonX : 0 ≤ epsilonX) (hk : 0 < k) (hell : 0 < ell) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp 1 ≤ T ∧ 8 ≤ pintz2023SourceLambda T k ∧
      ∀ gamma : ℝ, 1 ≤ |gamma| →
        2 * pintz2023SourceLambda T k ≤ |gamma| →
        (harmonic (pintz2023SourceX T epsilonX ell) : ℝ) * |gamma|⁻¹ *
          Real.exp (eta ^ 2 / pintz2023SourceLambda T k +
            pintz2023SourceLambda T k * eta -
            gamma ^ 2 / pintz2023SourceLambda T k) ≤ 1 / 8 := by
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  have hConstant : 0 ≤
      (1 + epsilonX / (10 * (ell : ℝ))) * Real.exp (eta ^ 2 / 8) := by
    positivity
  have hSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (p := 1) (q := 6 / (k : ℝ)) hConstant
      (div_pos (by norm_num) hkReal)
      (by norm_num : (0 : ℝ) < 1 / 8)
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact (Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal))
  filter_upwards [hSmall, eventually_ge_atTop (Real.exp 1),
    hLambda.eventually (eventually_ge_atTop 8)] with T hSmallT hT hLam
  refine ⟨hT, hLam, ?_⟩
  intro gamma hgammaOne hgammaLambda
  have hEnvelope := pintz2023_pole_scale_le_source_envelope hT hepsilonX
    hk hell heta hetaUpper hLam hgammaOne hgammaLambda
  refine hEnvelope.trans ?_
  rw [← Real.rpow_one (Real.log T)]
  simpa only [show -(6 / (k : ℝ)) = -6 / (k : ℝ) by ring] using hSmallT

theorem eventually_pintz2023_remainder_scale_le_eighth
    {K : ℝ} {k : ℕ} (hK : 0 ≤ K) (hk : 0 < k) :
    ∀ᶠ T : ℝ in atTop,
      K * Real.exp (-2 * pintz2023SourceLambda T k) ≤ 1 / 8 := by
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (p := 0) (q := 4 / (k : ℝ)) hK
      (div_pos (by norm_num) hkReal)
      (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [hSmall, eventually_gt_atTop 0] with T hSmallT hT
  rw [exp_neg_two_pintz2023SourceLambda hT hk]
  simpa only [Real.rpow_zero, mul_one,
    show -(4 / (k : ℝ)) = -4 / (k : ℝ) by ring] using hSmallT

#print axioms eventually_const_mul_log_rpow_mul_negative_rpow_le
#print axioms eventually_pintz2023_detector_envelope_le_eighth
#print axioms eventually_pintz2023_left_scale_le_eighth
#print axioms pintz2023_pole_scale_le_source_envelope
#print axioms eventually_pintz2023_pole_scale_le_eighth
#print axioms eventually_pintz2023_remainder_scale_le_eighth

end

end GafniTao
