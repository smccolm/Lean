import GafniTao.Pintz2023LargeMSourceBound
import GafniTao.Pintz2023DetectorEventually

/-!
# Pintz equation (4.14): exponent and logarithm absorption

This file converts the exact `X^xi H_X N_k(2T)^(-3 epsilon)` output into
the displayed `T^(-2 epsilon/k)` error.  The spare half-power is retained
until the final logarithmic absorption.
-/

open Filter Asymptotics

namespace GafniTao

noncomputable section

theorem pintzCell_sourceX_exponent_le
    {eta xi epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hepsilon : 0 ≤ epsilon)
    (hxiEta : xi ≤ eta) :
    (epsilon / (10 * (ell : ℝ))) * xi ≤ epsilon / (2 * (k : ℝ)) := by
  have hk : 4 ≤ k := hcell.1
  have hell : 3 ≤ ell := hcell.2.1
  have hkPos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hellPos : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkMinus : (3 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hetaNonneg : 0 ≤ eta := (pintzCell_eta_pos hcell).le
  have hetaK : eta * (k : ℝ) < 1 := by
    have hupper := hcell.2.2.1
    have hmul : eta * (k : ℝ) ≤
        eta * (k : ℝ) * ((k : ℝ) - 1) := by
      nlinarith [mul_nonneg hetaNonneg hkPos.le]
    exact hmul.trans_lt hupper
  have hscale : (k : ℝ) * xi ≤ 5 * (ell : ℝ) := by
    have hxiK := mul_le_mul_of_nonneg_left hxiEta hkPos.le
    have hxiKOne : (k : ℝ) * xi < 1 := by
      calc
        (k : ℝ) * xi ≤ (k : ℝ) * eta := hxiK
        _ = eta * (k : ℝ) := by ring
        _ < 1 := hetaK
    have hFiveEll : (1 : ℝ) ≤ 5 * (ell : ℝ) := by
      have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hell
      nlinarith
    exact hxiKOne.le.trans hFiveEll
  rw [div_mul_eq_mul_div, div_le_div_iff₀
    (by positivity : (0 : ℝ) < 10 * ell)
    (by positivity : (0 : ℝ) < 2 * k)]
  nlinarith

theorem pintz2023_sourceX_rpow_single_le
    {T epsilon xi : ℝ} {ell : ℕ}
    (hT : 1 ≤ T) (hepsilon : 0 ≤ epsilon) (hell : 0 < ell)
    (hxi : 0 ≤ xi) :
    (pintz2023SourceX T epsilon ell : ℝ) ^ xi ≤
      T ^ ((epsilon / (10 * (ell : ℝ))) * xi) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  let a : ℝ := epsilon / (10 * (ell : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hXle : (pintz2023SourceX T epsilon ell : ℝ) ≤ T ^ a := by
    simpa only [a] using pintz2023SourceX_cast_le
      (Real.rpow_pos_of_pos hTPos _).le
  have hXnonneg : (0 : ℝ) ≤ pintz2023SourceX T epsilon ell := by positivity
  calc
    (pintz2023SourceX T epsilon ell : ℝ) ^ xi ≤
        (T ^ a) ^ xi := Real.rpow_le_rpow hXnonneg hXle hxi
    _ = T ^ (a * xi) := (Real.rpow_mul hTPos.le a xi).symm
    _ = T ^ ((epsilon / (10 * (ell : ℝ))) * xi) := rfl

theorem pintz2023CriticalScale_neg_three_le
    {T eta epsilon : ℝ} {k : ℕ}
    (hT : 1 ≤ T) (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hk : 0 < k)
    (hmargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta) :
    (pintz2023CriticalScale k eta epsilon (2 * T)) ^ (-3 * epsilon) ≤
      T ^ (-3 * epsilon / (k : ℝ)) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hTwoTPos : 0 < 2 * T := by positivity
  have hTwoTOne : 1 ≤ 2 * T := by linarith
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  let d : ℝ := 1 - ((k : ℝ) - 1) * eta - 6 * (k : ℝ) * epsilon
  have hd : 0 < d := by dsimp only [d]; linarith
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkMinus : 0 ≤ (k : ℝ) - 1 := by linarith
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    have hfirst : 0 ≤ ((k : ℝ) - 1) * eta := mul_nonneg hkMinus heta.le
    have hsecond : 0 ≤ 6 * (k : ℝ) * epsilon := by positivity
    linarith
  have hdenOrder : (k : ℝ) * d ≤ (k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hdOne hkReal.le]
  have hexponent : 1 / (k : ℝ) ≤
      pintz2023CriticalScaleExponent k eta epsilon := by
    unfold pintz2023CriticalScaleExponent
    dsimp only [d] at hdenOrder ⊢
    exact one_div_le_one_div_of_le (mul_pos hkReal hd) hdenOrder
  have hLowerAtTwoT : (2 * T) ^ (1 / (k : ℝ)) ≤
      pintz2023CriticalScale k eta epsilon (2 * T) := by
    unfold pintz2023CriticalScale
    exact Real.rpow_le_rpow_of_exponent_le hTwoTOne hexponent
  have hBaseMono : T ^ (1 / (k : ℝ)) ≤ (2 * T) ^ (1 / (k : ℝ)) := by
    exact Real.rpow_le_rpow hTPos.le (by linarith)
      (by positivity)
  have hLower : T ^ (1 / (k : ℝ)) ≤
      pintz2023CriticalScale k eta epsilon (2 * T) :=
    hBaseMono.trans hLowerAtTwoT
  have hnegative : -3 * epsilon ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hTPos _) hLower hnegative
  calc
    (pintz2023CriticalScale k eta epsilon (2 * T)) ^ (-3 * epsilon) ≤
        (T ^ (1 / (k : ℝ))) ^ (-3 * epsilon) := hpow
    _ = T ^ ((1 / (k : ℝ)) * (-3 * epsilon)) :=
      (Real.rpow_mul hTPos.le _ _).symm
    _ = T ^ (-3 * epsilon / (k : ℝ)) := by congr 1; field_simp

theorem eventually_pintz2023_largeM_envelope
    {eta epsilon C : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hepsilon : 0 < epsilon)
    (hC : 0 ≤ C)
    (hmargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta) :
    ∀ᶠ T : ℝ in atTop, ∀ xi : ℝ, 0 ≤ xi → xi ≤ eta →
      C * (pintz2023SourceX T epsilon ell : ℝ) ^ xi *
          ((harmonic (pintz2023SourceX T epsilon ell) : ℚ) : ℝ) *
          (pintz2023CriticalScale k eta epsilon (2 * T)) ^
            (-3 * epsilon) ≤
        T ^ (-2 * epsilon / (k : ℝ)) := by
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
  let D : ℝ := C * (1 + epsilon / (10 * (ell : ℝ)))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hsmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := D) (p := 1) (q := epsilon / (2 * (k : ℝ))) (b := 1)
    hD (by positivity) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1)] with T hsmallT hT
  intro xi hxi hxiEta
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hTOne : 1 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp 1 := by
      rw [← Real.exp_zero]
      exact (Real.exp_lt_exp.mpr (by norm_num)).le
    linarith
  have hXpow := pintz2023_sourceX_rpow_single_le
    hTOne hepsilon.le hell hxi
  have hExponent := pintzCell_sourceX_exponent_le
    hcell hepsilon.le hxiEta
  have hXpow' : (pintz2023SourceX T epsilon ell : ℝ) ^ xi ≤
      T ^ (epsilon / (2 * (k : ℝ))) :=
    hXpow.trans (Real.rpow_le_rpow_of_exponent_le hTOne hExponent)
  have hHarm := harmonic_pintz2023SourceX_le
    hT hepsilon.le hell
  have hQpow := pintz2023CriticalScale_neg_three_le
    hTOne (pintzCell_eta_pos hcell) hepsilon hk hmargin
  have hlogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne
  have hHarmNonneg : 0 ≤
      ((harmonic (pintz2023SourceX T epsilon ell) : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg fun i _hi => inv_nonneg.mpr (Nat.cast_nonneg i)
  have hXNonneg : 0 ≤ (pintz2023SourceX T epsilon ell : ℝ) ^ xi :=
    Real.rpow_nonneg (by positivity) _
  have hQNonneg : 0 ≤
      (pintz2023CriticalScale k eta epsilon (2 * T)) ^ (-3 * epsilon) :=
    Real.rpow_nonneg (Real.rpow_nonneg (by positivity) _) _
  calc
    C * (pintz2023SourceX T epsilon ell : ℝ) ^ xi *
          ((harmonic (pintz2023SourceX T epsilon ell) : ℚ) : ℝ) *
          (pintz2023CriticalScale k eta epsilon (2 * T)) ^ (-3 * epsilon) ≤
        C * T ^ (epsilon / (2 * (k : ℝ))) *
          ((1 + epsilon / (10 * (ell : ℝ))) * Real.log T) *
          T ^ (-3 * epsilon / (k : ℝ)) := by
      gcongr
    _ = D * Real.log T *
          (T ^ (epsilon / (2 * (k : ℝ))) *
            T ^ (-3 * epsilon / (k : ℝ))) := by
      dsimp only [D]
      ring
    _ = D * Real.log T * T ^ (-5 * epsilon / (2 * (k : ℝ))) := by
      rw [← Real.rpow_add hTPos]
      congr 2
      field_simp
      ring
    _ = (D * Real.log T ^ (1 : ℝ) *
          T ^ (-(epsilon / (2 * (k : ℝ))))) *
          T ^ (-2 * epsilon / (k : ℝ)) := by
      have hsplit : T ^ (-5 * epsilon / (2 * (k : ℝ))) =
          T ^ (-(epsilon / (2 * (k : ℝ)))) *
            T ^ (-2 * epsilon / (k : ℝ)) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        field_simp
        ring
      rw [Real.rpow_one, hsplit]
      ring
    _ ≤ 1 * T ^ (-2 * epsilon / (k : ℝ)) := by
      gcongr
    _ = T ^ (-2 * epsilon / (k : ℝ)) := one_mul _

/-- The displayed equation-(4.14) estimate for every nonempty localized
source block and every detected exponent on the cell. -/
theorem eventually_pintz2023_largeM_localized_le
    {eta epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell) (hepsilon : 0 < epsilon)
    (hAlpha : eta + 6 * epsilon < pintz2023HBAlpha k)
    (hmargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta) :
    ∀ᶠ T : ℝ in atTop, ∀ (xi t : ℝ) (q : ℕ),
      0 ≤ xi → xi ≤ eta →
      T / 4 < |t| → |t| ≤ T + 2 * pintz2023SourceLambda T k →
      2 ^ q * pintz2023SourceX T epsilon ell ≤
        min (2 * (2 ^ q * pintz2023SourceX T epsilon ell))
          (pintz2023Cutoff (pintz2023SourceLambda T k)) + 1 →
      ‖pintz2023SplitIntervalBlock
          (fun n => pintz2023LargeMCoeff
            (pintz2023SourceX T epsilon ell) n
            (pintz2023CriticalScale k eta epsilon (2 * T)))
          (pintz2023LocalizedInterval
            (pintz2023SourceX T epsilon ell)
            (pintz2023Cutoff (pintz2023SourceLambda T k)) q)
          (((1 - xi : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤
        T ^ (-2 * epsilon / (k : ℝ)) := by
  have hkFour : 4 ≤ k := hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  obtain ⟨C, hC, hSource⟩ :=
    pintz2023_largeM_localized_source_bound k epsilon hkFour hepsilon
  have hEnvelope := eventually_pintz2023_largeM_envelope
    hcell hepsilon hC.le hmargin
  filter_upwards [hEnvelope, eventually_eight_mul_log_le_identity,
    eventually_ge_atTop (4 : ℝ)] with T hEnvelopeT hLogT hT
  intro xi t q hxi hxiEta hPhysical hUpper hNonempty
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hTFour : 4 ≤ T := hT
  have hLambdaLeLog : pintz2023SourceLambda T k ≤ Real.log T := by
    unfold pintz2023SourceLambda
    have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hkFour
    have hratio : 2 / (k : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith)
    exact mul_le_of_le_one_left (Real.log_nonneg hTOne) hratio
  have hShiftUpper : T + 2 * pintz2023SourceLambda T k ≤ 2 * T := by
    nlinarith
  have hX : 1 ≤ pintz2023SourceX T epsilon ell := by
    apply pintz2023SourceX_pos
    exact Real.one_le_rpow hTOne (by positivity)
  have hden : 0 < 1 - ((k : ℝ) - 1) * eta -
      6 * (k : ℝ) * epsilon := by linarith
  have hraw := hSource T eta xi t (pintz2023SourceX T epsilon ell) q
    hTFour (pintzCell_eta_pos hcell).le hxiEta hAlpha hden hxi
    hShiftUpper hPhysical hUpper hX hNonempty
  exact hraw.trans (hEnvelopeT xi hxi hxiEta)

#print axioms pintzCell_sourceX_exponent_le
#print axioms pintz2023_sourceX_rpow_single_le
#print axioms pintz2023CriticalScale_neg_three_le
#print axioms eventually_pintz2023_largeM_envelope
#print axioms eventually_pintz2023_largeM_localized_le

end

end GafniTao
