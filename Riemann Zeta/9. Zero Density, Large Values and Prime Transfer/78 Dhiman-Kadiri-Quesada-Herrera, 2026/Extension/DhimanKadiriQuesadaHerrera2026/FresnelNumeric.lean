import DhimanKadiriQuesadaHerrera2026.StationaryTaylor
import DhimanKadiriQuesadaHerrera2026.QuadraticStationary

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- A global upper polynomial for the cosine comes from the actual eighth-derivative Taylor remainder. -/
theorem cos_le_taylor_eight (x : ℝ) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have ht := taylor_remainder_of_differentiable (f := Real.cos) (a := 0) (x := x) 7
    (fun k _ u _ => (Real.differentiable_iteratedDeriv_cos k).differentiableAt)
    (fun u _ => Real.abs_iteratedDeriv_cos_le_one 8 u)
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    iteratedDeriv_succ, Real.deriv_cos, Real.deriv_sin, deriv.neg', Pi.neg_apply] at ht
  have h := (le_abs_self _).trans ht
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 8)] at h
  linarith

/-- The squared norm of the actual Fresnel segment is an iterated real cosine integral. -/
theorem norm_fresnel_segment_sq (x : ℝ) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      ∫ t in (0 : ℝ)..x, ∫ s in (0 : ℝ)..x, Real.cos (t ^ 2 - s ^ 2) := by
  have hc : Continuous (fun t : ℝ => Real.cos (t ^ 2)) := by fun_prop
  have hs : Continuous (fun t : ℝ => Real.sin (t ^ 2)) := by fun_prop
  have hk : Continuous (fun t : ℝ => Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hr := intervalIntegral.intervalIntegral_re (hk.intervalIntegrable (μ := volume) 0 x)
  have hi := intervalIntegral.intervalIntegral_im (hk.intervalIntegrable (μ := volume) 0 x)
  simp only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hr hi
  rw [Complex.sq_norm, Complex.normSq_apply, ← hr, ← hi]
  simp_rw [Real.cos_sub]
  have he (t : ℝ) : (∫ s in (0 : ℝ)..x,
      (Real.cos (t ^ 2) * Real.cos (s ^ 2) + Real.sin (t ^ 2) * Real.sin (s ^ 2))) =
      Real.cos (t ^ 2) * (∫ s in (0 : ℝ)..x, Real.cos (s ^ 2)) +
        Real.sin (t ^ 2) * (∫ s in (0 : ℝ)..x, Real.sin (s ^ 2)) := by
    rw [intervalIntegral.integral_add ((hc.const_mul _).intervalIntegrable 0 x)
      ((hs.const_mul _).intervalIntegrable 0 x), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp_rw [he]
  rw [intervalIntegral.integral_add ((hc.mul_const _).intervalIntegrable 0 x)
    ((hs.mul_const _).intervalIntegrable 0 x), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]

/-- The iterated eighth-order cosine polynomial integrates to an explicit ninth-degree polynomial in x². -/
theorem integral_fresnel_cos_polynomial (x : ℝ) :
    (∫ t in (0 : ℝ)..x, ∫ s in (0 : ℝ)..x,
      (1 - (t ^ 2 - s ^ 2) ^ 2 / 2 + (t ^ 2 - s ^ 2) ^ 4 / 24 -
        (t ^ 2 - s ^ 2) ^ 6 / 720 + (t ^ 2 - s ^ 2) ^ 8 / 40320)) =
      x ^ 2 - 4 * x ^ 6 / 45 + 16 * x ^ 10 / 4725 -
        64 * x ^ 14 / 945945 + 256 * x ^ 18 / 310134825 := by
  have he (t s : ℝ) :
      1 - (t ^ 2 - s ^ 2) ^ 2 / 2 + (t ^ 2 - s ^ 2) ^ 4 / 24 -
        (t ^ 2 - s ^ 2) ^ 6 / 720 + (t ^ 2 - s ^ 2) ^ 8 / 40320 =
      (1 / 1 : ℝ) * t ^ 0 * s ^ 0 +
        (-1 / 2 : ℝ) * t ^ 4 * s ^ 0 +
        (1 / 1 : ℝ) * t ^ 2 * s ^ 2 +
        (-1 / 2 : ℝ) * t ^ 0 * s ^ 4 +
        (1 / 24 : ℝ) * t ^ 8 * s ^ 0 +
        (-1 / 6 : ℝ) * t ^ 6 * s ^ 2 +
        (1 / 4 : ℝ) * t ^ 4 * s ^ 4 +
        (-1 / 6 : ℝ) * t ^ 2 * s ^ 6 +
        (1 / 24 : ℝ) * t ^ 0 * s ^ 8 +
        (-1 / 720 : ℝ) * t ^ 12 * s ^ 0 +
        (1 / 120 : ℝ) * t ^ 10 * s ^ 2 +
        (-1 / 48 : ℝ) * t ^ 8 * s ^ 4 +
        (1 / 36 : ℝ) * t ^ 6 * s ^ 6 +
        (-1 / 48 : ℝ) * t ^ 4 * s ^ 8 +
        (1 / 120 : ℝ) * t ^ 2 * s ^ 10 +
        (-1 / 720 : ℝ) * t ^ 0 * s ^ 12 +
        (1 / 40320 : ℝ) * t ^ 16 * s ^ 0 +
        (-1 / 5040 : ℝ) * t ^ 14 * s ^ 2 +
        (1 / 1440 : ℝ) * t ^ 12 * s ^ 4 +
        (-1 / 720 : ℝ) * t ^ 10 * s ^ 6 +
        (1 / 576 : ℝ) * t ^ 8 * s ^ 8 +
        (-1 / 720 : ℝ) * t ^ 6 * s ^ 10 +
        (1 / 1440 : ℝ) * t ^ 4 * s ^ 12 +
        (-1 / 5040 : ℝ) * t ^ 2 * s ^ 14 +
        (1 / 40320 : ℝ) * t ^ 0 * s ^ 16 := by ring
  simp_rw [he]
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, integral_pow, zero_add, Nat.cast_ofNat]
  ring

/-- The actual Fresnel norm is bounded by integrating the proved cosine upper polynomial. -/
theorem norm_fresnel_segment_sq_le_polynomial {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      x ^ 2 - 4 * x ^ 6 / 45 + 16 * x ^ 10 / 4725 -
        64 * x ^ 14 / 945945 + 256 * x ^ 18 / 310134825 := by
  rw [norm_fresnel_segment_sq, ← integral_fresnel_cos_polynomial]
  apply intervalIntegral.integral_mono_on hx
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · intro t ht
    apply intervalIntegral.integral_mono_on hx
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
    · intro u hu
      exact cos_le_taylor_eight _

/-- Four rational Bernstein certificates cover the entire finite parameter interval. -/
theorem fresnel_norm_polynomial_le {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ 1089 / 400) :
    z - 4 * z ^ 3 / 45 + 16 * z ^ 5 / 4725 - 64 * z ^ 7 / 945945 +
      256 * z ^ 9 / 310134825 ≤ (119 / 100 : ℝ) ^ 2 := by
  by_cases h0 : z ≤ (1089 / 800 : ℝ)
  · have hlo : 0 ≤ z - (0 / 1 : ℝ) := by linarith
    have hhi : 0 ≤ (1089 / 800 : ℝ) - z := by linarith
    have he : (119 / 100 : ℝ) ^ 2 -
        (z - 4 * z ^ 3 / 45 + 16 * z ^ 5 / 4725 - 64 * z ^ 7 / 945945 +
          256 * z ^ 9 / 310134825) =
        (190065724620800000000000000 / 2154025884392726618070214209 : ℝ) * (z - (0 / 1 : ℝ)) ^ 0 * ((1089 / 800 : ℝ) - z) ^ 9 +
        (169765293260800000000000000 / 239336209376969624230023801 : ℝ) * (z - (0 / 1 : ℝ)) ^ 1 * ((1089 / 800 : ℝ) - z) ^ 8 +
        (199286482534400000000000000 / 79778736458989874743341267 : ℝ) * (z - (0 / 1 : ℝ)) ^ 2 * ((1089 / 800 : ℝ) - z) ^ 7 +
        (3626635183416934400000000000 / 718008628130908872690071403 : ℝ) * (z - (0 / 1 : ℝ)) ^ 3 * ((1089 / 800 : ℝ) - z) ^ 6 +
        (1544158245080268800000000000 / 239336209376969624230023801 : ℝ) * (z - (0 / 1 : ℝ)) ^ 4 * ((1089 / 800 : ℝ) - z) ^ 5 +
        (3009555632123365031936000000 / 558451155212929123203388869 : ℝ) * (z - (0 / 1 : ℝ)) ^ 5 * ((1089 / 800 : ℝ) - z) ^ 4 +
        (14764105828627509149696000000 / 5026060396916362108830499821 : ℝ) * (z - (0 / 1 : ℝ)) ^ 6 * ((1089 / 800 : ℝ) - z) ^ 3 +
        (153261559837952915028975616000 / 152457165373129650634525161237 : ℝ) * (z - (0 / 1 : ℝ)) ^ 7 * ((1089 / 800 : ℝ) - z) ^ 2 +
        (3312249294772645545525248000 / 16939685041458850070502795693 : ℝ) * (z - (0 / 1 : ℝ)) ^ 8 * ((1089 / 800 : ℝ) - z) ^ 1 +
        (737367211994485113292573970176 / 44857589042478531821312210902425 : ℝ) * (z - (0 / 1 : ℝ)) ^ 9 * ((1089 / 800 : ℝ) - z) ^ 0 := by ring
    apply sub_nonneg.mp
    rw [he]
    positivity
  by_cases h1 : z ≤ (3267 / 1600 : ℝ)
  · have hlo : 0 ≤ z - (1089 / 800 : ℝ) := by linarith
    have hhi : 0 ≤ (3267 / 1600 : ℝ) - z := by linarith
    have he : (119 / 100 : ℝ) ^ 2 -
        (z - 4 * z ^ 3 / 45 + 16 * z ^ 5 / 4725 - 64 * z ^ 7 / 945945 +
          256 * z ^ 9 / 310134825) =
        (377532012541176378005797872730112 / 44857589042478531821312210902425 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 0 * ((3267 / 1600 : ℝ) - z) ^ 9 +
        (1372839911703854950978245225545728 / 21598098427860033839891064508575 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 1 * ((3267 / 1600 : ℝ) - z) ^ 8 +
        (13588420209205780586114750520623104 / 64794295283580101519673193525725 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 2 * ((3267 / 1600 : ℝ) - z) ^ 7 +
        (1569162639055361244709076448247808 / 3966997670423271521612644501575 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 3 * ((3267 / 1600 : ℝ) - z) ^ 6 +
        (1444743004193903423259870690033664 / 3085442632551433405698723501225 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 4 * ((3267 / 1600 : ℝ) - z) ^ 5 +
        (3323140813120546512452459129151488 / 9256327897654300217096170503675 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 5 * ((3267 / 1600 : ℝ) - z) ^ 4 +
        (4920136075534979434126628305854464 / 27768983692962900651288511511025 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 6 * ((3267 / 1600 : ℝ) - z) ^ 3 +
        (129265219021309200527121103925248 / 2399788714206670426654562723175 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 7 * ((3267 / 1600 : ℝ) - z) ^ 2 +
        (588534543546304490716965446043136 / 64794295283580101519673193525725 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 8 * ((3267 / 1600 : ℝ) - z) ^ 1 +
        (376888829413049560427178242664704 / 583148657552220913677058741731525 : ℝ) * (z - (1089 / 800 : ℝ)) ^ 9 * ((3267 / 1600 : ℝ) - z) ^ 0 := by ring
    apply sub_nonneg.mp
    rw [he]
    positivity
  by_cases h2 : z ≤ (7623 / 3200 : ℝ)
  · have hlo : 0 ≤ z - (3267 / 1600 : ℝ) := by linarith
    have hhi : 0 ≤ (7623 / 3200 : ℝ) - z := by linarith
    have he : (119 / 100 : ℝ) ^ 2 -
        (z - 4 * z ^ 3 / 45 + 16 * z ^ 5 / 4725 - 64 * z ^ 7 / 945945 +
          256 * z ^ 9 / 310134825) =
        (192967080659481374938715260244328448 / 583148657552220913677058741731525 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 0 * ((7623 / 3200 : ℝ) - z) ^ 9 +
        (138785777841368112784529736179449856 / 64794295283580101519673193525725 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 1 * ((7623 / 3200 : ℝ) - z) ^ 8 +
        (125155401699576525329216675706699776 / 21598098427860033839891064508575 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 2 * ((7623 / 3200 : ℝ) - z) ^ 7 +
        (232548801296103924650674046919049216 / 27768983692962900651288511511025 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 3 * ((7623 / 3200 : ℝ) - z) ^ 6 +
        (63014335531434748361674016700645376 / 9256327897654300217096170503675 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 4 * ((7623 / 3200 : ℝ) - z) ^ 5 +
        (440247349856481952897025917804544 / 146925839645306352652320166725 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 5 * ((7623 / 3200 : ℝ) - z) ^ 4 +
        (2910070142351628081370593003495424 / 3966997670423271521612644501575 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 6 * ((7623 / 3200 : ℝ) - z) ^ 3 +
        (411249179216759275519349713915904 / 1322332556807757173870881500525 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 7 * ((7623 / 3200 : ℝ) - z) ^ 2 +
        (92125753552997393325934448141824 / 440777518935919057956960500175 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 8 * ((7623 / 3200 : ℝ) - z) ^ 1 +
        (621006122814691207567328981296384 / 11900993011269814564837933504725 : ℝ) * (z - (3267 / 1600 : ℝ)) ^ 9 * ((7623 / 3200 : ℝ) - z) ^ 0 := by ring
    apply sub_nonneg.mp
    rw [he]
    positivity
  have hlo : 0 ≤ z - (7623 / 3200 : ℝ) := by linarith
  have hhi : 0 ≤ (1089 / 400 : ℝ) - z := by linarith
  have he : (119 / 100 : ℝ) ^ 2 -
      (z - 4 * z ^ 3 / 45 + 16 * z ^ 5 / 4725 - 64 * z ^ 7 / 945945 +
        256 * z ^ 9 / 310134825) =
      (621006122814691207567328981296384 / 11900993011269814564837933504725 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 0 * ((1089 / 400 : ℝ) - z) ^ 9 +
      (965634984970390235156854618167296 / 1322332556807757173870881500525 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 1 * ((1089 / 400 : ℝ) - z) ^ 8 +
      (1975103657902647905650586634616832 / 440777518935919057956960500175 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 2 * ((1089 / 400 : ℝ) - z) ^ 7 +
      (60605007313821719512981863064403968 / 3966997670423271521612644501575 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 3 * ((1089 / 400 : ℝ) - z) ^ 6 +
      (42155235368771938259242030722973696 / 1322332556807757173870881500525 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 4 * ((1089 / 400 : ℝ) - z) ^ 5 +
      (43739727088238007388295577261309952 / 1028480877517144468566241167075 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 5 * ((1089 / 400 : ℝ) - z) ^ 4 +
      (1014758233080231947644381340404547584 / 27768983692962900651288511511025 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 6 * ((1089 / 400 : ℝ) - z) ^ 3 +
      (1271540267163625963854242425755140096 / 64794295283580101519673193525725 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 7 * ((1089 / 400 : ℝ) - z) ^ 2 +
      (129720042382049400808598991013937152 / 21598098427860033839891064508575 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 8 * ((1089 / 400 : ℝ) - z) ^ 1 +
      (467245508563075245575494616077041664 / 583148657552220913677058741731525 : ℝ) * (z - (7623 / 3200 : ℝ)) ^ 9 * ((1089 / 400 : ℝ) - z) ^ 0 := by ring
  apply sub_nonneg.mp
  rw [he]
  positivity

/-- The entire finite Fresnel segment has a certified norm bound, without sampling. -/
theorem norm_fresnel_segment_le_finite {x : ℝ} (hx : 0 ≤ x) (hxu : x ≤ 33 / 20) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 119 / 100 := by
  have hp := fresnel_norm_polynomial_le (sq_nonneg x) (by nlinarith : x ^ 2 ≤ 1089 / 400)
  have hn := norm_fresnel_segment_sq_le_polynomial hx
  simp only [← pow_mul] at hp
  norm_num only [Nat.reduceMul] at hp
  nlinarith [norm_nonneg (∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I))]

/-- The evaluated Fresnel limit and sharp tail control every positive distant endpoint. -/
theorem norm_fresnel_segment_le_tail {x : ℝ} (hx : 0 < x) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.sqrt Real.pi / 2 + 1 / (2 * x) := by
  let K : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * ((0 + (-1 / Real.pi) * t ^ 2 / 2 : ℝ) : ℂ))
  let M : ℂ := (Complex.exp (2 * Real.pi * Complex.I * ((0 - 1 / 8 : ℝ) : ℂ)) /
    (Real.sqrt |(-1 / Real.pi : ℝ)| : ℂ)) / 2
  have hκ : (-1 / Real.pi : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) Real.pi_pos
  have h := quadratic_half_window_sharp 0 hκ hx
  change ‖(∫ t in (0 : ℝ)..x, K t) - M‖ ≤ _ at h
  have he (t : ℝ) : K t = (starRingEnd ℂ) (Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) := by
    dsimp [K]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    field_simp
    ring
  have hi : (∫ t in (0 : ℝ)..x, K t) =
      (starRingEnd ℂ) (∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) := by
    simp_rw [he]
    simp only [intervalIntegral, integral_conj, map_sub]
  have hm : ‖M‖ = Real.sqrt Real.pi / 2 := by
    have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((0 - 1 / 8 : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      norm_num [Complex.mul_re, Complex.mul_im]
    dsimp [M]
    rw [norm_div, norm_div, he]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_ofNat]
    rw [abs_of_neg hκ, neg_div, neg_neg, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, one_div_one_div]
  have hb : 1 / (2 * Real.pi * |(-1 / Real.pi : ℝ)| * x) = 1 / (2 * x) := by
    rw [abs_of_neg hκ]
    field_simp
  have hn : ‖∫ t in (0 : ℝ)..x, K t‖ ≤ ‖(∫ t in (0 : ℝ)..x, K t) - M‖ + ‖M‖ := by
    calc
      _ = ‖((∫ t in (0 : ℝ)..x, K t) - M) + M‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [hi, Complex.norm_conj, hm] at hn
  rw [hi, hb] at h
  linarith

/-- The global finite Fresnel primitive has the certified numerical bound 1.19. -/
theorem norm_fresnel_segment_le {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 119 / 100 := by
  by_cases hxu : x ≤ 33 / 20
  · exact norm_fresnel_segment_le_finite hx hxu
  · have hp : 0 < x := by linarith
    have htail := norm_fresnel_segment_le_tail hp
    have hs : Real.sqrt Real.pi ≤ 1773 / 1000 := by
      nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_lt_d4]
    have hr : 1 / (2 * x) ≤ 10 / 33 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * x)).mpr
      linarith
    linarith

/-- Reversing an even phase extends the certified primitive bound to every real endpoint. -/
theorem norm_fresnel_segment_le_all (x : ℝ) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 119 / 100 := by
  by_cases hx : 0 ≤ x
  · exact norm_fresnel_segment_le hx
  · have he : (∫ t in (0 : ℝ)..x, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) =
        -(∫ t in (0 : ℝ)..(-x), Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) := by
      have hh := intervalIntegral.integral_comp_neg
        (fun t : ℝ => Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) (a := 0) (b := x)
      simp only [neg_sq, neg_zero] at hh
      rw [hh, intervalIntegral.integral_symm]
    rw [he, norm_neg]
    exact norm_fresnel_segment_le (by linarith)

/-- Any finite Fresnel interval has the certified doubled primitive bound. -/
theorem norm_fresnel_interval_le (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤ 119 / 50 := by
  have hk : Continuous (fun t : ℝ => Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hk.intervalIntegrable (μ := volume) 0 a) (hk.intervalIntegrable a b)
  have hi : (∫ t in a..b, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) =
      (∫ t in (0 : ℝ)..b, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) -
        (∫ t in (0 : ℝ)..a, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) := by rw [← he]; ring
  rw [hi]
  have hn := norm_sub_le (∫ t in (0 : ℝ)..b, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I))
    (∫ t in (0 : ℝ)..a, Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I))
  linarith [norm_fresnel_segment_le_all a, norm_fresnel_segment_le_all b]

/-- Scaling the actual Fresnel interval retains the inverse square-root dependence. -/
theorem norm_scaled_fresnel_interval_le {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((ρ * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      119 / (50 * Real.sqrt ρ) := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have he (t : ℝ) : ρ * t ^ 2 = (Real.sqrt ρ * t) ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ.le]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) hs.ne',
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  apply (mul_le_mul_of_nonneg_left (norm_fresnel_interval_le _ _) (inv_nonneg.mpr hs.le)).trans_eq
  ring

/-- Complex conjugation gives the same certified bound for negative quadratic phase. -/
theorem norm_negative_fresnel_interval_le {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((-ρ * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      119 / (50 * Real.sqrt ρ) := by
  have he (t : ℝ) : Complex.exp (((-ρ * t ^ 2 : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (((ρ * t ^ 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  simp_rw [he]
  have hi : (∫ t in a..b, (starRingEnd ℂ) (Complex.exp (((ρ * t ^ 2 : ℝ) : ℂ) * Complex.I))) =
      (starRingEnd ℂ) (∫ t in a..b, Complex.exp (((ρ * t ^ 2 : ℝ) : ℂ) * Complex.I)) := by
    simp only [intervalIntegral, integral_conj, map_sub]
  rw [hi, Complex.norm_conj]
  exact norm_scaled_fresnel_interval_le hρ a b

/-- The source 1.343 constant is certified for every genuine quadratic phase interval. -/
theorem quadratic_integral_bound_1343 (A a b : ℝ) {κ : ℝ} (hκ : κ < 0) :
    ‖∫ t in a..b, Complex.exp (2 * Real.pi * Complex.I * ((A + κ * t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      1.343 / Real.sqrt |κ| := by
  have hk : 0 < |κ| := abs_pos.mpr (ne_of_lt hκ)
  have hp : 0 < Real.pi * |κ| := mul_pos Real.pi_pos hk
  have he (t : ℝ) : Complex.exp (2 * Real.pi * Complex.I * ((A + κ * t ^ 2 / 2 : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (A : ℂ)) *
        Complex.exp (((-(Real.pi * |κ|) * t ^ 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, abs_of_neg hκ]
    congr 1
    push_cast
    ring
  have hn : ‖Complex.exp (2 * Real.pi * Complex.I * (A : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re, Complex.mul_im]
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [norm_mul, hn, one_mul]
  apply (norm_negative_fresnel_interval_le hp a b).trans
  rw [Real.sqrt_mul Real.pi_pos.le]
  have hc : (119 / 50 : ℝ) ≤ 1.343 * Real.sqrt Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_d4]
  have hsκ : 0 < Real.sqrt |κ| := Real.sqrt_pos.mpr hk
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  apply (div_le_iff₀ (by positivity : 0 < 50 * (Real.sqrt Real.pi * Real.sqrt |κ|))).mpr
  have hm := mul_le_mul_of_nonneg_right hc hsκ.le
  field_simp
  nlinarith

/-- Scaling the primitive, rather than a general interval, retains half of the global quadratic constant. -/
theorem norm_scaled_fresnel_segment_le {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (((ρ * t ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      119 / (100 * Real.sqrt ρ) := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have he (t : ℝ) : ρ * t ^ 2 = (Real.sqrt ρ * t) ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ.le]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => Complex.exp (((t ^ 2 : ℝ) : ℂ) * Complex.I)) hs.ne',
    mul_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  apply (mul_le_mul_of_nonneg_left (norm_fresnel_segment_le_all _) (inv_nonneg.mpr hs.le)).trans_eq
  ring

/-- Every real projection of a quadratic prefix is bounded by the certified half constant. -/
theorem quadratic_cos_prefix_le (θ x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ t in (0 : ℝ)..x, Real.cos (θ + ρ * t ^ 2)) ≤ 119 / (100 * Real.sqrt ρ) := by
  have hk : Continuous (fun t : ℝ => Complex.exp (((θ + ρ * t ^ 2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hr := intervalIntegral.intervalIntegral_re (hk.intervalIntegrable (μ := volume) 0 x)
  simp only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] at hr
  rw [hr]
  apply (Complex.re_le_norm _).trans
  have he (t : ℝ) : Complex.exp (((θ + ρ * t ^ 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((ρ * t ^ 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_scaled_fresnel_segment_le hρ x

end DhimanKadiriQuesadaHerrera2026
