import Tao2026.SmoothNumberSaddlePerronComplement

/-!
# Growth of the smooth saddle main term

This module gives an elementary upper bound for the saddle curvature on the
critical half-plane, derives a concrete lower bound for the Gaussian saddle
main term, and proves that main term diverges in every critical regime.  The
bounded Perron endpoint correction therefore vanishes after normalization,
so the source saddle asymptotic is equivalent to decay of the explicit
complementary Perron line.
-/

open Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

theorem smoothSaddlePhiTwo_le_seven_log_mul_phiOne
    (y : ℕ) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    smoothSaddlePhiTwo y sigma ≤
      7 * Real.log y * smoothSaddlePhiOne y sigma := by
  unfold smoothSaddlePhiTwo smoothSaddlePhiOne
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpIcc := (Finset.mem_filter.mp hp).1
  have hpTwo : 2 ≤ p := (Finset.mem_Icc.mp hpIcc).1
  have hpy : p ≤ y := (Finset.mem_Icc.mp hpIcc).2
  have hsigmaPos : 0 < sigma := by linarith
  have hden := smoothSaddle_denominator_pos hpTwo hsigmaPos
  have hqpos : 0 < (p : ℝ) ^ sigma := by positivity
  have hratio : (p : ℝ) ^ sigma / ((p : ℝ) ^ sigma - 1) ≤ 7 := by
    calc
      (p : ℝ) ^ sigma / ((p : ℝ) ^ sigma - 1) ≤
          ((p : ℝ) ^ sigma + 1) / ((p : ℝ) ^ sigma - 1) := by
        exact div_le_div_of_nonneg_right (by linarith) hden.le
      _ ≤ 7 := prime_rpow_add_one_div_sub_one_le_seven hpTwo hsigma
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < p by omega))).le
  have hlogpy : Real.log (p : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpy)
  have hprime : 0 ≤ smoothSaddlePrimeTerm p sigma :=
    (smoothSaddlePrimeTerm_pos hpTwo hsigmaPos).le
  have hid : smoothSaddleSecondPrimeTerm p sigma =
      Real.log p * ((p : ℝ) ^ sigma / ((p : ℝ) ^ sigma - 1)) *
        smoothSaddlePrimeTerm p sigma := by
    unfold smoothSaddleSecondPrimeTerm smoothSaddlePrimeTerm
    field_simp [hden.ne']
  rw [hid]
  calc
    Real.log p * ((p : ℝ) ^ sigma / ((p : ℝ) ^ sigma - 1)) *
          smoothSaddlePrimeTerm p sigma ≤
        Real.log y * 7 * smoothSaddlePrimeTerm p sigma := by
      gcongr
    _ = 7 * Real.log y * smoothSaddlePrimeTerm p sigma := by ring

theorem smoothSaddlePhiTwo_saddle_le_seven_log_mul_log
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) :
    smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
      7 * Real.log y * Real.log X := by
  rw [← smoothSaddlePhiOne_smoothSaddlePoint hX hy]
  exact smoothSaddlePhiTwo_le_seven_log_mul_phiOne y hsigma

theorem smoothSaddlePhiZero_nonneg
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 ≤ smoothSaddlePhiZero y sigma := by
  unfold smoothSaddlePhiZero
  apply Finset.sum_nonneg
  intro p hp
  have hpTwo : 2 ≤ p :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hbase := smoothEulerFactorBase_pos hpTwo hsigma
  have hbaseLe : 1 - (p : ℝ) ^ (-sigma) ≤ 1 := by
    exact sub_le_self _ (Real.rpow_nonneg (by positivity) _)
  exact neg_nonneg.mpr (Real.log_nonpos hbase.le hbaseLe)

theorem rpow_le_exp_smoothSaddlePhase
    {X y : ℕ} (hX : 1 ≤ X) {sigma : ℝ} (hsigma : 0 < sigma) :
    (X : ℝ) ^ sigma ≤ Real.exp (smoothSaddlePhase X y sigma) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < X by omega))]
  apply Real.exp_le_exp.mpr
  unfold smoothSaddlePhase
  nlinarith [smoothSaddlePhiZero_nonneg y hsigma]

theorem sqrt_fourteen_pi_mul_log_sq
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (14 * Real.pi * x ^ 2) =
      Real.sqrt (14 * Real.pi) * x := by
  rw [show 14 * Real.pi * x ^ 2 = (14 * Real.pi) * x ^ 2 by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 14 * Real.pi),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

theorem smoothSaddleMainTerm_lower_bound
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (hyX : y ≤ X)
    (hsigmaLower : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaUpper : smoothSaddlePoint X y ≤ 1) :
    (X : ℝ) ^ (1 / 2 : ℝ) /
        (Real.sqrt (14 * Real.pi) * Real.log X) ≤
      smoothSaddleMainTerm X y := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hlogyX : Real.log (y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hyX)
  have hphi := smoothSaddlePhiTwo_saddle_le_seven_log_mul_log
    hX hy hsigmaLower
  have hphiBound : smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
      7 * (Real.log X) ^ 2 := by
    calc
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
          7 * Real.log y * Real.log X := hphi
      _ ≤ 7 * (Real.log X) ^ 2 := by nlinarith
  have hinside :
      2 * Real.pi * smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
        14 * Real.pi * (Real.log X) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hphiBound
      (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith
  have hsqrt :
      Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
        Real.sqrt (14 * Real.pi) * Real.log X := by
    calc
      Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
          Real.sqrt (14 * Real.pi * (Real.log X) ^ 2) :=
        Real.sqrt_le_sqrt hinside
      _ = Real.sqrt (14 * Real.pi) * Real.log X :=
        sqrt_fourteen_pi_mul_log_sq hlogX.le
  have hden : smoothSaddlePoint X y *
        Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
      Real.sqrt (14 * Real.pi) * Real.log X := by
    calc
      smoothSaddlePoint X y * Real.sqrt (2 * Real.pi *
          smoothSaddlePhiTwo y (smoothSaddlePoint X y)) ≤
          1 * Real.sqrt (2 * Real.pi *
            smoothSaddlePhiTwo y (smoothSaddlePoint X y)) := by
        gcongr
      _ ≤ Real.sqrt (14 * Real.pi) * Real.log X := by simpa using hsqrt
  have hnum : (X : ℝ) ^ (1 / 2 : ℝ) ≤
      Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) := by
    exact (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ X by omega)) hsigmaLower).trans
        (rpow_le_exp_smoothSaddlePhase (show 1 ≤ X by omega) hsigma)
  have hdenPos : 0 < smoothSaddlePoint X y *
      Real.sqrt (2 * Real.pi *
        smoothSaddlePhiTwo y (smoothSaddlePoint X y)) := by
    exact mul_pos hsigma (Real.sqrt_pos.2 (mul_pos
      (mul_pos (by norm_num) Real.pi_pos)
      (smoothSaddlePhiTwo_pos hy hsigma)))
  have hupperDenPos : 0 < Real.sqrt (14 * Real.pi) * Real.log X :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hlogX
  unfold smoothSaddleMainTerm
  rw [div_le_div_iff₀ hupperDenPos hdenPos]
  exact mul_le_mul hnum hden hdenPos.le (Real.exp_pos _).le

theorem tendsto_sqrt_div_sqrt_fourteen_pi_mul_log_atTop :
    Tendsto (fun x : ℝ =>
      x ^ (1 / 2 : ℝ) / (Real.sqrt (14 * Real.pi) * Real.log x))
      atTop atTop := by
  have hsmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 4)).def (by norm_num : (0 : ℝ) < 1)
  have hquarter : Tendsto (fun x : ℝ => x ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hC : 0 < Real.sqrt (14 * Real.pi) :=
    Real.sqrt_pos.2 (by positivity)
  rw [tendsto_atTop]
  intro b
  filter_upwards [hsmall,
    hquarter.eventually (eventually_ge_atTop
      (Real.sqrt (14 * Real.pi) * max b 0)),
    eventually_ge_atTop (2 : ℝ)] with x hlog hroot hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hrootnonneg : 0 ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg hxpos.le _
  have hlogle : Real.log x ≤ x ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogpos.le,
      abs_of_nonneg hrootnonneg, one_mul] using hlog
  have hsqrt : x ^ (1 / 2 : ℝ) =
      x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  rw [le_div_iff₀ (mul_pos hC hlogpos), hsqrt]
  have hbC : b * Real.sqrt (14 * Real.pi) ≤
      x ^ (1 / 4 : ℝ) := by
    calc
      b * Real.sqrt (14 * Real.pi) ≤
          Real.sqrt (14 * Real.pi) * max b 0 := by
        rw [mul_comm b]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
      _ ≤ x ^ (1 / 4 : ℝ) := hroot
  nlinarith

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleMainTerm_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleMainTerm (X n) (y n)) atTop atTop := by
  have hlower : Tendsto (fun n =>
      (X n : ℝ) ^ (1 / 2 : ℝ) /
        (Real.sqrt (14 * Real.pi) * Real.log (X n))) atTop atTop :=
    tendsto_sqrt_div_sqrt_fourteen_pi_mul_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hregime.tendsto_X_atTop)
  refine tendsto_atTop_mono' atTop ?_ hlower
  have hsigmaLower : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ smoothSaddlePoint (X n) (y n) :=
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hsigmaUpper : ∀ᶠ n in atTop,
      smoothSaddlePoint (X n) (y n) ≤ 1 :=
    (hregime.eventually_smoothSaddlePoint_lt_one hα).mono
      (fun _ h => h.le)
  have hyX : ∀ᶠ n in atTop, y n ≤ X n := by
    have hratio := (hregime.tendsto_log_y_div_log_X_zero hα).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hratio, hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hratio hX hy
    have hlogX : 0 < Real.log (X n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X n by omega))
    have hlogyX : Real.log (y n : ℝ) < Real.log (X n : ℝ) := by
      rw [div_lt_one hlogX] at hratio
      exact hratio
    have hypos : (0 : ℝ) < y n := by
      exact_mod_cast (show 0 < y n by omega)
    have hXpos : (0 : ℝ) < X n := by
      exact_mod_cast (show 0 < X n by omega)
    have hreal : (y n : ℝ) ≤ X n :=
      (Real.strictMonoOn_log.le_iff_le
        (show (y n : ℝ) ∈ Set.Ioi 0 from hypos)
        (show (X n : ℝ) ∈ Set.Ioi 0 from hXpos)).mp hlogyX.le
    exact_mod_cast hreal
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα, hsigmaLower, hsigmaUpper, hyX] with
      n hX hy hslo hshi hyX
  exact smoothSaddleMainTerm_lower_bound hX hy hyX hslo hshi

theorem IsTaoCriticalSmoothRegime.tendsto_smoothPerronEndpointCorrection_div_mainTerm_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothPerronEndpointCorrection (X n) (y n) /
        (smoothSaddleMainTerm (X n) (y n) : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : Tendsto (fun n =>
      (1 / 2 : ℝ) / smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (hregime.tendsto_smoothSaddleMainTerm_atTop hα)
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  exact norm_smoothPerronEndpointCorrection_div_mainTerm_le hX hy

theorem IsTaoCriticalSmoothRegime.tendsto_infiniteComplementaryPerronLine_zero_iff_ratio
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleInfiniteComplementaryPerronLine (X n) (y n))
        atTop (𝓝 0) ↔
      Tendsto (fun n =>
        (psiNat (X n) (y n) : ℂ) /
          (smoothSaddleMainTerm (X n) (y n) : ℂ)) atTop (𝓝 1) := by
  rw [hregime.tendsto_infiniteComplementaryPerronLine_zero_iff hα]
  have hendpoint :=
    hregime.tendsto_smoothPerronEndpointCorrection_div_mainTerm_zero hα
  constructor
  · intro hcorrected
    have hsum := hcorrected.add hendpoint
    have heq : (fun n =>
        ((psiNat (X n) (y n) : ℂ) -
            smoothPerronEndpointCorrection (X n) (y n)) /
              (smoothSaddleMainTerm (X n) (y n) : ℂ) +
          smoothPerronEndpointCorrection (X n) (y n) /
            (smoothSaddleMainTerm (X n) (y n) : ℂ)) =
        (fun n => (psiNat (X n) (y n) : ℂ) /
          (smoothSaddleMainTerm (X n) (y n) : ℂ)) := by
      funext n
      ring
    rw [heq] at hsum
    simpa only [add_zero] using hsum
  · intro hratio
    have hdiff := hratio.sub hendpoint
    have heq : (fun n =>
        (psiNat (X n) (y n) : ℂ) /
            (smoothSaddleMainTerm (X n) (y n) : ℂ) -
          smoothPerronEndpointCorrection (X n) (y n) /
            (smoothSaddleMainTerm (X n) (y n) : ℂ)) =
        (fun n => ((psiNat (X n) (y n) : ℂ) -
            smoothPerronEndpointCorrection (X n) (y n)) /
          (smoothSaddleMainTerm (X n) (y n) : ℂ)) := by
      funext n
      ring
    rw [heq] at hdiff
    simpa only [sub_zero] using hdiff

theorem criticalSmoothSaddleAsymptotic_iff_infiniteComplementaryPerronLine :
    TaoCriticalSmoothSaddleAsymptoticConclusion ↔
      ∀ (α : ℝ) (X y : ℕ → ℕ), 0 < α →
        IsTaoCriticalSmoothRegime X y α →
          Tendsto (fun n =>
            smoothSaddleInfiniteComplementaryPerronLine (X n) (y n))
              atTop (𝓝 0) := by
  constructor
  · intro hasymptotic α X y hα hregime
    rw [hregime.tendsto_infiniteComplementaryPerronLine_zero_iff_ratio hα]
    have hreal := hasymptotic α X y hα hregime
    have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    change Tendsto (fun n => Complex.ofReal
      ((psiNat (X n) (y n) : ℝ) /
        smoothSaddleMainTerm (X n) (y n))) atTop (𝓝 (Complex.ofReal 1))
      at hcomplex
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_one] using hcomplex
  · intro htail α X y hα hregime
    have hcomplex :=
      (hregime.tendsto_infiniteComplementaryPerronLine_zero_iff_ratio hα).mp
        (htail α X y hα hregime)
    have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
    change Tendsto (fun n =>
      ((psiNat (X n) (y n) : ℂ) /
        (smoothSaddleMainTerm (X n) (y n) : ℂ)).re)
      atTop (𝓝 (1 : ℂ).re) at hreal
    have heq : (fun n =>
        ((psiNat (X n) (y n) : ℂ) /
          (smoothSaddleMainTerm (X n) (y n) : ℂ)).re) =
        (fun n => (psiNat (X n) (y n) : ℝ) /
          smoothSaddleMainTerm (X n) (y n)) := by
      funext n
      change (Complex.ofReal (psiNat (X n) (y n) : ℝ) /
          Complex.ofReal (smoothSaddleMainTerm (X n) (y n))).re = _
      rw [← Complex.ofReal_div]
      norm_num
    rw [heq] at hreal
    simpa using hreal

end

end Tao2026
