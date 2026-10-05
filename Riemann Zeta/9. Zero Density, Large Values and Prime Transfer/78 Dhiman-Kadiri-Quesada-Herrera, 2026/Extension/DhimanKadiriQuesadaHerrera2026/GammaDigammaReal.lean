import DhimanKadiriQuesadaHerrera2026.EulerMaclaurin

/-! # Real-part digamma estimates on a horizontal gamma segment

The reciprocal kernel is the actual real part of `1 / (u + it)`.
Finite Euler--Maclaurin identities retain their endpoint terms.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory Filter
open scoped BigOperators Topology

/-- The real part of the nonreal reciprocal appearing in the digamma series. -/
noncomputable def gammaReciprocal (t u : ℝ) : ℝ := u / (u ^ 2 + t ^ 2)

/-- Its actual derivative, whose sign changes only at u=t on the positive axis. -/
noncomputable def gammaReciprocalDeriv (t u : ℝ) : ℝ :=
  (t ^ 2 - u ^ 2) / (u ^ 2 + t ^ 2) ^ 2

/-- Positive height keeps every reciprocal denominator away from zero. -/
theorem gammaReciprocal_den_pos {t : ℝ} (ht : 0 < t) (u : ℝ) :
    0 < u ^ 2 + t ^ 2 := by positivity

/-- The kernel is exactly the real part required by the complex digamma function. -/
theorem gammaReciprocal_eq_re (t u : ℝ) :
    gammaReciprocal t u = (1 / ((u : ℂ) + (t : ℂ) * Complex.I)).re := by
  simp [gammaReciprocal, Complex.normSq_apply, sq]

/-- Differentiation of the actual reciprocal kernel. -/
theorem gammaReciprocal_hasDerivAt {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (gammaReciprocal t) (gammaReciprocalDeriv t u) u := by
  have hd := (hasDerivAt_id u).div
    (((hasDerivAt_id u).pow 2).add_const (t ^ 2)) (gammaReciprocal_den_pos ht u).ne'
  convert hd using 1
  dsimp [gammaReciprocalDeriv]
  congr 1
  ring

/-- Continuity of the actual reciprocal kernel at positive height. -/
theorem continuous_gammaReciprocal {t : ℝ} (ht : 0 < t) :
    Continuous (gammaReciprocal t) :=
  continuous_iff_continuousAt.mpr fun u => (gammaReciprocal_hasDerivAt ht u).continuousAt

/-- The derivative is continuous on the entire real axis at a positive height. -/
theorem continuous_gammaReciprocalDeriv {t : ℝ} (ht : 0 < t) :
    Continuous (gammaReciprocalDeriv t) := by
  unfold gammaReciprocalDeriv
  exact (continuous_const.sub (continuous_id.pow 2)).div
    ((continuous_id.pow 2).add continuous_const |>.pow 2)
    (fun u => pow_ne_zero 2 (gammaReciprocal_den_pos ht u).ne')

/-- The logarithmic antiderivative is valid even when the real part is zero. -/
theorem gammaReciprocal_log_hasDerivAt {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.log (v ^ 2 + t ^ 2) / 2) (gammaReciprocal t u) u := by
  have hd := ((((hasDerivAt_id u).pow 2).add_const (t ^ 2)).log
    (gammaReciprocal_den_pos ht u).ne').div_const 2
  convert hd using 1
  dsimp [gammaReciprocal]
  ring

/-- The actual reciprocal integral is a difference of real logarithms. -/
theorem integral_gammaReciprocal {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    (∫ u in a..b, gammaReciprocal t u) =
      Real.log (b ^ 2 + t ^ 2) / 2 - Real.log (a ^ 2 + t ^ 2) / 2 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => gammaReciprocal_log_hasDerivAt ht u)
    ((continuous_gammaReciprocal ht).intervalIntegrable a b)

/-- A finite trapezoidal identity with the exact first-order Bernoulli remainder. -/
theorem sum_range_trapezoid_identity (f : ℝ → ℝ) (N : ℕ)
    (hd : ∀ u ∈ Set.Icc 0 (N : ℝ), DifferentiableAt ℝ f u)
    (hc : ContinuousOn (deriv f) (Set.Icc 0 (N : ℝ))) :
    (∑ n ∈ Finset.range N, f n) = (f 0 - f N) / 2 +
      (∫ u in (0 : ℝ)..N, f u) + ∫ u in (0 : ℝ)..N, deriv f u * B1 u := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have he := sum_eq_integral_add_integral_deriv (f := f) (by norm_num : (0 : ℝ) ≤ 0)
    hn hd (by simpa only [Set.uIcc_of_le hn] using hc)
  simp only [Nat.floor_zero, Nat.floor_natCast] at he
  have hb0 : B1 0 = -1 / 2 := by norm_num [B1]
  have hbN : B1 (N : ℝ) = -1 / 2 := by norm_num [B1]
  rw [hb0, hbN] at he
  have hsum : (∑ n ∈ Finset.Ioc 0 N, f n) + f 0 =
      (∑ n ∈ Finset.range N, f n) + f N := by
    have hs : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hs, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1]
    simpa only [Nat.cast_zero] using
      (Finset.sum_range_succ' (fun n : ℕ => f (n : ℝ)) N).symm.trans
        (Finset.sum_range_succ (fun n : ℕ => f (n : ℝ)) N)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at he
  linarith

/-- The trapezoidal error is at most half the total variation of a continuously differentiable function. -/
theorem abs_sum_range_trapezoid_error_le (f : ℝ → ℝ) (N : ℕ)
    (hd : ∀ u ∈ Set.Icc 0 (N : ℝ), DifferentiableAt ℝ f u)
    (hc : ContinuousOn (deriv f) (Set.Icc 0 (N : ℝ))) :
    |(∑ n ∈ Finset.range N, f n) - (f 0 - f N) / 2 -
      (∫ u in (0 : ℝ)..N, f u)| ≤ (∫ u in (0 : ℝ)..N, |deriv f u|) / 2 := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [sum_range_trapezoid_identity f N hd hc]
  rw [show (f 0 - f N) / 2 + (∫ u in (0 : ℝ)..N, f u) +
      (∫ u in (0 : ℝ)..N, deriv f u * B1 u) - (f 0 - f N) / 2 -
      (∫ u in (0 : ℝ)..N, f u) = ∫ u in (0 : ℝ)..N, deriv f u * B1 u by ring]
  have hb : IntervalIntegrable (fun u => |deriv f u| / 2) volume 0 N := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hn] using hc.abs.div_const 2
  have hi := intervalIntegral.norm_integral_le_of_norm_le hn
    (f := fun u => deriv f u * B1 u) (g := fun u => |deriv f u| / 2)
    (Filter.Eventually.of_forall fun u hu => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ |deriv f u| * (1 / 2) := mul_le_mul_of_nonneg_left
          (abs_B1_le_half hu.1.le) (abs_nonneg _)
        _ = _ := by ring) hb
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_div] using hi

/-- Exact integration of the reciprocal derivative on any finite interval. -/
theorem integral_gammaReciprocalDeriv {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    (∫ u in a..b, gammaReciprocalDeriv t u) = gammaReciprocal t b - gammaReciprocal t a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => gammaReciprocal_hasDerivAt ht u)
    ((continuous_gammaReciprocalDeriv ht).intervalIntegrable a b)

/-- The reciprocal increases up to the unique positive critical point. -/
theorem gammaReciprocalDeriv_nonneg {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    0 ≤ gammaReciprocalDeriv t u := by
  unfold gammaReciprocalDeriv
  apply div_nonneg _ (sq_nonneg _)
  nlinarith

/-- After the critical point, the reciprocal decreases. -/
theorem gammaReciprocalDeriv_nonpos {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    gammaReciprocalDeriv t u ≤ 0 := by
  unfold gammaReciprocalDeriv
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  nlinarith

/-- Total variation on the increasing part of the reciprocal kernel. -/
theorem integral_abs_gammaReciprocalDeriv_of_le {t a b : ℝ} (ht : 0 < t)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) :
    (∫ u in a..b, |gammaReciprocalDeriv t u|) =
      gammaReciprocal t b - gammaReciprocal t a := by
  rw [← integral_gammaReciprocalDeriv ht]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  exact abs_of_nonneg (gammaReciprocalDeriv_nonneg (ha.trans hu.1) (hu.2.trans hbt))

/-- Total variation on the decreasing part of the reciprocal kernel. -/
theorem integral_abs_gammaReciprocalDeriv_of_ge {t a b : ℝ} (ht : 0 < t)
    (hta : t ≤ a) (hab : a ≤ b) :
    (∫ u in a..b, |gammaReciprocalDeriv t u|) =
      gammaReciprocal t a - gammaReciprocal t b := by
  have hi : (∫ u in a..b, |gammaReciprocalDeriv t u|) =
      ∫ u in a..b, -gammaReciprocalDeriv t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact abs_of_nonpos (gammaReciprocalDeriv_nonpos ht.le (hta.trans hu.1))
  rw [hi, intervalIntegral.integral_neg, integral_gammaReciprocalDeriv ht]
  ring

/-- The reciprocal kernel has maximum 1/(2t) at its critical point. -/
theorem gammaReciprocal_self {t : ℝ} (ht : 0 < t) :
    gammaReciprocal t t = 1 / (2 * t) := by
  unfold gammaReciprocal
  field_simp
  ring

/-- Total variation across the critical point, retaining both endpoint corrections. -/
theorem integral_abs_gammaReciprocalDeriv_cross {t a b : ℝ} (ht : 0 < t)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    (∫ u in a..b, |gammaReciprocalDeriv t u|) =
      1 / t - gammaReciprocal t a - gammaReciprocal t b := by
  have hcont := (continuous_gammaReciprocalDeriv ht).abs
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable a t) (hcont.intervalIntegrable t b),
    integral_abs_gammaReciprocalDeriv_of_le ht ha hat le_rfl,
    integral_abs_gammaReciprocalDeriv_of_ge ht le_rfl htb, gammaReciprocal_self ht]
  ring

/-- The real part of the actual digamma series, with no restriction on the real part. -/
theorem hasSum_gammaReciprocal_difference {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - gammaReciprocal t ((n : ℝ) + x))
      ((Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re +
        Real.eulerMascheroniConstant) := by
  have hpoles (n : ℕ) : (x : ℂ) + (t : ℂ) * Complex.I ≠ -(n : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  convert Complex.hasSum_re (Complex.hasSum_digamma hpoles) using 1
  funext n
  rw [Complex.sub_re, gammaReciprocal_eq_re]
  have hr : (1 / ((n : ℂ) + 1)).re = 1 / ((n : ℝ) + 1) := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hr]
  congr 2
  push_cast
  ring

/-- The real digamma value is the limit of the actual finite reciprocal correction. -/
theorem tendsto_log_sub_gammaReciprocal_sum {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Tendsto (fun N : ℕ => Real.log N -
      ∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x)) atTop
      (𝓝 (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re) := by
  have h := (hasSum_gammaReciprocal_difference ht x).tendsto_sum_nat.sub
    Real.tendsto_harmonic_sub_log
  convert h using 1
  · funext N
    rw [Finset.sum_sub_distrib]
    simp only [one_div, Complex.sum_inv_natCast_add_one_real]
    ring
  · congr 1
    ring

/-- The endpoint logarithm has the same asymptotic normalization as log N. -/
theorem tendsto_log_quadratic_sub_log {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Tendsto (fun N : ℕ => Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 - Real.log N)
      atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => (1 + x / (N : ℝ)) ^ 2 + (t / (N : ℝ)) ^ 2)
      atTop (𝓝 1) := by
    convert ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat x)).pow 2).add
      ((tendsto_const_div_atTop_nhds_zero_nat t).pow 2) using 1
    norm_num
  have hl := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr).div_const 2
  simp only [Real.log_one, zero_div] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he : (1 + x / (N : ℝ)) ^ 2 + (t / (N : ℝ)) ^ 2 =
      (((N : ℝ) + x) ^ 2 + t ^ 2) / (N : ℝ) ^ 2 := by field_simp
  dsimp only [Function.comp_apply]
  rw [he, Real.log_div (gammaReciprocal_den_pos ht _).ne' (pow_ne_zero 2 hn), Real.log_pow]
  ring

/-- Combining the finite reciprocal and logarithmic limits gives the actual digamma value. -/
theorem tendsto_log_quadratic_sub_gammaReciprocal_sum {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Tendsto (fun N : ℕ => Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 -
      ∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x)) atTop
      (𝓝 (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re) := by
  convert (tendsto_log_sub_gammaReciprocal_sum ht x).add
    (tendsto_log_quadratic_sub_log ht x) using 1
  · funext N
    ring
  · simp

/-- Specializing the trapezoidal comparison retains the true shifted reciprocal and its variation. -/
theorem gammaReciprocal_trapezoid_error {t : ℝ} (ht : 0 < t) (x : ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x)) -
      (gammaReciprocal t x - gammaReciprocal t ((N : ℝ) + x)) / 2 -
      (Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 - Real.log (x ^ 2 + t ^ 2) / 2)| ≤
      (∫ u in x..((N : ℝ) + x), |gammaReciprocalDeriv t u|) / 2 := by
  have hd (u : ℝ) : HasDerivAt (fun v => gammaReciprocal t (v + x))
      (gammaReciprocalDeriv t (u + x)) u := by
    simpa only [mul_one] using (gammaReciprocal_hasDerivAt ht (u + x)).comp u
      ((hasDerivAt_id u).add_const x)
  have he : deriv (fun v => gammaReciprocal t (v + x)) =
      fun u => gammaReciprocalDeriv t (u + x) := funext fun u => (hd u).deriv
  have h := abs_sum_range_trapezoid_error_le (fun v => gammaReciprocal t (v + x)) N
    (fun u _ => (hd u).differentiableAt) (by
      rw [he]
      exact ((continuous_gammaReciprocalDeriv ht).comp (continuous_id.add_const x)).continuousOn)
  rw [he] at h
  dsimp only at h
  rw [intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_comp_add_right (fun u => |gammaReciprocalDeriv t u|)] at h
  simp only [zero_add] at h
  rwa [integral_gammaReciprocal ht] at h

/-- Before the reciprocal maximum, the digamma real part has both sharp endpoint corrections. -/
theorem re_digamma_bounds_before_peak {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) (hxt : x ≤ t) :
    Real.log (x ^ 2 + t ^ 2) / 2 - 1 / (2 * t) ≤
      (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re ∧
    (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re ≤
      Real.log (x ^ 2 + t ^ 2) / 2 - gammaReciprocal t x + 1 / (2 * t) := by
  have hevent : ∀ᶠ N : ℕ in atTop, t ≤ (N : ℝ) + x := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop t)] with N hN
    linarith
  have hb : ∀ᶠ N : ℕ in atTop,
      Real.log (x ^ 2 + t ^ 2) / 2 - 1 / (2 * t) ≤
        Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 -
          ∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x) ∧
      Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 -
          ∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x) ≤
        Real.log (x ^ 2 + t ^ 2) / 2 - gammaReciprocal t x + 1 / (2 * t) := by
    filter_upwards [hevent] with N hN
    have h := gammaReciprocal_trapezoid_error ht x N
    rw [integral_abs_gammaReciprocalDeriv_cross ht hx hxt hN] at h
    have habs := abs_le.mp h
    have hpos : 0 ≤ gammaReciprocal t ((N : ℝ) + x) := by
      unfold gammaReciprocal
      positivity
    have htwo : 1 / (2 * t) = (1 / t) / 2 := by ring
    rw [htwo]
    constructor <;> linarith [habs.1, habs.2]
  exact ⟨ge_of_tendsto (tendsto_log_quadratic_sub_gammaReciprocal_sum ht x)
    (hb.mono fun _ h => h.1), le_of_tendsto (tendsto_log_quadratic_sub_gammaReciprocal_sum ht x)
      (hb.mono fun _ h => h.2)⟩

/-- Beyond the reciprocal maximum, the finite variation bound loses no extra constant. -/
theorem re_digamma_bounds_after_peak {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    Real.log (x ^ 2 + t ^ 2) / 2 - gammaReciprocal t x ≤
      (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re ∧
    (Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re ≤
      Real.log (x ^ 2 + t ^ 2) / 2 := by
  have hb (N : ℕ) :
      Real.log (x ^ 2 + t ^ 2) / 2 - gammaReciprocal t x ≤
        Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 -
          ∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x) ∧
      Real.log (((N : ℝ) + x) ^ 2 + t ^ 2) / 2 -
          ∑ n ∈ Finset.range N, gammaReciprocal t ((n : ℝ) + x) ≤
        Real.log (x ^ 2 + t ^ 2) / 2 := by
    have h := gammaReciprocal_trapezoid_error ht x N
    rw [integral_abs_gammaReciprocalDeriv_of_ge ht htx (by have := Nat.cast_nonneg (α := ℝ) N; linarith)] at h
    have habs := abs_le.mp h
    have hpos : 0 ≤ gammaReciprocal t ((N : ℝ) + x) := by
      unfold gammaReciprocal
      have hx := ht.le.trans htx
      positivity
    constructor <;> linarith [habs.1, habs.2]
  exact ⟨ge_of_tendsto (tendsto_log_quadratic_sub_gammaReciprocal_sum ht x)
    (Filter.Eventually.of_forall fun N => (hb N).1),
    le_of_tendsto (tendsto_log_quadratic_sub_gammaReciprocal_sum ht x)
      (Filter.Eventually.of_forall fun N => (hb N).2)⟩

/-- The logarithm of the modulus has its exact positive-height normalization. -/
theorem log_quadratic_eq_log_height {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.log (x ^ 2 + t ^ 2) / 2 = Real.log t + Real.log (1 + (x / t) ^ 2) / 2 := by
  have he : 1 + (x / t) ^ 2 = (x ^ 2 + t ^ 2) / t ^ 2 := by
    field_simp
    ring
  rw [he, Real.log_div (gammaReciprocal_den_pos ht x).ne' (pow_ne_zero 2 ht.ne'),
    Real.log_pow]
  ring

/-- The endpoint logarithm is bounded below by the height logarithm. -/
theorem log_quadratic_ge_log_height {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.log t ≤ Real.log (x ^ 2 + t ^ 2) / 2 := by
  rw [log_quadratic_eq_log_height ht]
  have hlog := Real.log_nonneg (show 1 ≤ 1 + (x / t) ^ 2 by nlinarith [sq_nonneg (x / t)])
  linarith

/-- The reciprocal kernel never exceeds its critical value. -/
theorem gammaReciprocal_le_peak {t : ℝ} (ht : 0 < t) (x : ℝ) :
    gammaReciprocal t x ≤ 1 / (2 * t) := by
  unfold gammaReciprocal
  rw [div_le_div_iff₀ (gammaReciprocal_den_pos ht x) (by positivity : 0 < 2 * t)]
  nlinarith [sq_nonneg (x - t)]

/-- Before the reciprocal peak, its endpoint correction absorbs the logarithmic displacement. -/
theorem log_quadratic_le_log_add_reciprocal {t x : ℝ} (ht : 0 < t)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hxt : x ≤ t) :
    Real.log (x ^ 2 + t ^ 2) / 2 ≤ Real.log t + gammaReciprocal t x := by
  rw [log_quadratic_eq_log_height ht]
  have hl : Real.log (1 + (x / t) ^ 2) ≤ (x / t) ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (x / t) ^ 2 by positivity)
    linarith
  have hx2 : x ^ 2 ≤ x := by nlinarith
  have hxt2 : x ^ 2 ≤ t ^ 2 := by nlinarith
  have hm : x ^ 2 * (x ^ 2 + t ^ 2) ≤ 2 * x * t ^ 2 := by
    calc
      _ ≤ x * (x ^ 2 + t ^ 2) := mul_le_mul_of_nonneg_right hx2 (by positivity)
      _ ≤ x * (2 * t ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hx
      _ = _ := by ring
  have hr : (x / t) ^ 2 / 2 ≤ gammaReciprocal t x := by
    unfold gammaReciprocal
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity : 0 < t ^ 2 * 2)
      (gammaReciprocal_den_pos ht x)]
    nlinarith [hm]
  linarith

/-- A logarithmic displacement of real part at most one half costs at most 1/(2t). -/
theorem log_quadratic_le_log_add_half_inv {t x : ℝ} (ht : 0 < t)
    (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    Real.log (x ^ 2 + t ^ 2) / 2 ≤ Real.log t + 1 / (2 * t) := by
  rw [log_quadratic_eq_log_height ht]
  have hv : 0 ≤ x / t := div_nonneg hx.1 ht.le
  have hl := Real.log_le_log (show 0 < 1 + (x / t) ^ 2 by positivity)
    (show 1 + (x / t) ^ 2 ≤ (1 + x / t) ^ 2 by nlinarith)
  rw [Real.log_pow] at hl
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + x / t by positivity)
  have hdiv : x / t ≤ 1 / (2 * t) := by
    rw [div_le_div_iff₀ ht (by positivity : 0 < 2 * t)]
    nlinarith [hx.2]
  linarith

/-- A uniform explicit real-part digamma estimate on the full Gamma segment, including its endpoint. -/
theorem abs_re_digamma_sub_log_height_le {t x : ℝ} (ht : 0 < t)
    (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    |(Complex.digamma ((x : ℂ) + (t : ℂ) * Complex.I)).re - Real.log t| ≤ 1 / (2 * t) := by
  apply abs_le.mpr
  have hlo := log_quadratic_ge_log_height ht x
  rcases le_total x t with hxt | htx
  · have h := re_digamma_bounds_before_peak ht hx.1 hxt
    have hu := log_quadratic_le_log_add_reciprocal ht hx.1 (by linarith [hx.2]) hxt
    constructor <;> linarith [h.1, h.2]
  · have h := re_digamma_bounds_after_peak ht htx
    have hu := log_quadratic_le_log_add_half_inv ht hx
    have hk := gammaReciprocal_le_peak ht x
    constructor <;> linarith [h.1, h.2]

end DhimanKadiriQuesadaHerrera2026
