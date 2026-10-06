import DhimanKadiriQuesadaHerrera2026.OscillatoryC3
import DhimanKadiriQuesadaHerrera2026.SecondCoefficients
import DhimanKadiriQuesadaHerrera2026.UpperModeTails

/-! # Actual constant-weight Fourier coefficients with cubic errors

The first boundary terms are combined before estimating the remainder, so the
resulting endpoint series retain their absolute convergence and cancellation.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- The actual positive Fourier coefficient is its first endpoint term minus its wave integral. -/
theorem positiveCoefficient_eq_boundary_sub_integral {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {n : ℕ} (hn : 0 < n) :
    positiveCoefficient f g a b n =
      weightedWave f g b * expMode (-b) n / (2 * Real.pi * Complex.I * n) -
      weightedWave f g a * expMode (-a) n / (2 * Real.pi * Complex.I * n) -
        ∫ x in a..b, weightedWave f g x * expMode (-x) n := by
  have hmode (x : ℝ) : HasDerivAt (fun u => expMode (-u) n)
      ((2 * Real.pi * Complex.I * n) * expMode (-x) n) x := by
    convert (hasDerivAt_expMode n (-x)).scomp x (hasDerivAt_neg x) using 1
    simp only [neg_smul, one_smul]
    ring
  have hm : Continuous (fun x => (2 * Real.pi * Complex.I * (n : ℂ)) * expMode (-x) n) := by
    unfold expMode
    fun_prop
  have hi : IntervalIntegrable (waveDerivative f g) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h.lt.le]
    exact h.waveDerivative_continuous
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hmode x) h.wave_hasDerivAt (hm.intervalIntegrable a b) hi
  have he1 : (fun x => expMode (-x) n * waveDerivative f g x) =
      fun x => waveDerivative f g x * expMode (-x) n := by funext x; ring
  have he2 : (fun x => (2 * Real.pi * Complex.I * (n : ℂ) * expMode (-x) n) * weightedWave f g x) =
      fun x => (2 * Real.pi * Complex.I * (n : ℂ)) * (weightedWave f g x * expMode (-x) n) := by
    funext x
    ring
  rw [he1, integral_waveDerivative_expMode_neg, he2, intervalIntegral.integral_const_mul] at hb
  unfold positiveCoefficient
  rw [hb]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp


/-- Multiplying the actual constant wave by a signed Fourier mode gives the shifted phase. -/
theorem constant_wave_mode (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    weightedWave f (fun _ => 1) x * expMode x n =
      exp (2 * Real.pi * I * ((f x - (n : ℝ) * x : ℝ) : ℂ)) := by
  simp only [weightedWave, Complex.ofReal_one, one_mul, expMode, ← exp_add]
  congr 1
  push_cast
  ring

/-- Positive modes have the corresponding plus phase. -/
theorem constant_wave_mode_neg (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    weightedWave f (fun _ => 1) x * expMode (-x) n =
      exp (2 * Real.pi * I * ((f x + (n : ℝ) * x : ℝ) : ℂ)) := by
  simp only [weightedWave, Complex.ofReal_one, one_mul, expMode, ← exp_add]
  congr 1
  push_cast
  ring

/-- Frequency translation preserves the actual cubic error under the source derivative hypotheses. -/
theorem norm_shifted_cubic {f : ℝ → ℝ} {a b κ D ρ ν : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hside : (∀ u ∈ Set.Icc a b, ρ ≤ deriv f u - ν) ∨ (∀ u ∈ Set.Icc a b, deriv f u - ν ≤ -ρ))
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, exp (2 * Real.pi * I * ((f u - ν * u : ℝ) : ℂ))) -
      (((1 / (deriv f b - ν) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f b - ν * b : ℝ) : ℂ)) -
        ((1 / (deriv f a - ν) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f a - ν * a : ℝ) : ℂ))) / (2 * Real.pi * I)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ρ ^ 3) := by
  exact norm_expMode_cubic (f := fun u => f u - ν * u) (p := fun u => deriv f u - ν)
    (k := deriv (deriv f)) hab hρ
    (fun u hu => by simpa only [id_eq, mul_one] using (hf u hu).hasDerivAt.sub ((hasDerivAt_id u).const_mul ν))
    (fun u hu => (hf' u hu).hasDerivAt.sub_const ν) hf'' hside hkneg hkb hD


set_option maxHeartbeats 800000 in
/-- The actual upper Poisson coefficient has cubic residual and its exact summable endpoint. -/
theorem negativeCoefficient_cubic {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : deriv f a < (M : ℝ) + 1) (n : ℕ) :
    ‖negativeCoefficient f (fun _ => 1) a b (n + M + 1) -
      (2 * Real.pi : ℂ) * (upperModeEndpoint f (deriv f) (deriv f) b M n -
        upperModeEndpoint f (deriv f) (deriv f) a M n)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ((n : ℝ) + M + 1 - deriv f a) ^ 3) := by
  have hρ : 0 < (n : ℝ) + M + 1 - deriv f a := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hside : ∀ u ∈ Set.Icc a b, deriv f u - ((n : ℝ) + M + 1) ≤ -((n : ℝ) + M + 1 - deriv f a) := by
    intro u hu
    have hh := h.f_deriv_antitone (Set.left_mem_Icc.mpr h.lt.le) hu hu.1
    linarith
  have hr := norm_shifted_cubic (ν := (n : ℝ) + M + 1) h.lt.le hρ h.f_differentiable hf' hf''
    (Or.inr hside) hkneg hkb hD
  have hjoin (u : ℝ) (hu : u ∈ Set.Icc a b) :
      exp (2 * Real.pi * I * ((f u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ)) /
        (2 * Real.pi * I * ((n : ℂ) + M + 1)) +
      (((1 / (deriv f u - ((n : ℝ) + M + 1)) : ℝ) : ℂ) *
        exp (2 * Real.pi * I * ((f u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) / (2 * Real.pi * I) =
      (2 * Real.pi : ℂ) * upperModeEndpoint f (deriv f) (deriv f) u M n := by
    have hg : deriv f u - ((n : ℝ) + M + 1) ≠ 0 := by linarith [hside u hu]
    have hgc : ((deriv f u : ℝ) : ℂ) - ((n : ℂ) + M + 1) ≠ 0 := by exact_mod_cast hg
    have hnc : (n : ℂ) + M + 1 ≠ 0 := by
      exact_mod_cast (show (n : ℝ) + M + 1 ≠ 0 by positivity)
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    unfold upperModeEndpoint
    push_cast
    field_simp
    ring
  rw [negativeCoefficient_eq_boundary_add_integral h (by omega)]
  simp_rw [constant_wave_mode]
  simp only [Nat.cast_add, Nat.cast_one]
  have hja := hjoin a (Set.left_mem_Icc.mpr h.lt.le)
  have hjb := hjoin b (Set.right_mem_Icc.mpr h.lt.le)
  have he : exp (2 * Real.pi * I * ((f b - ((n : ℝ) + M + 1) * b : ℝ) : ℂ)) /
        (2 * Real.pi * I * ((n : ℂ) + M + 1)) -
      exp (2 * Real.pi * I * ((f a - ((n : ℝ) + M + 1) * a : ℝ) : ℂ)) /
        (2 * Real.pi * I * ((n : ℂ) + M + 1)) +
      (∫ u in a..b, exp (2 * Real.pi * I * ((f u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) -
      (2 * Real.pi : ℂ) * (upperModeEndpoint f (deriv f) (deriv f) b M n -
        upperModeEndpoint f (deriv f) (deriv f) a M n) =
      (∫ u in a..b, exp (2 * Real.pi * I * ((f u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) -
      ((((1 / (deriv f b - ((n : ℝ) + M + 1)) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f b - ((n : ℝ) + M + 1) * b : ℝ) : ℂ))) -
        (((1 / (deriv f a - ((n : ℝ) + M + 1)) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f a - ((n : ℝ) + M + 1) * a : ℝ) : ℂ)))) / (2 * Real.pi * I) := by
    linear_combination hjb - hja
  rw [he]
  exact hr


set_option maxHeartbeats 800000 in
/-- The actual positive Poisson coefficient retains its summable endpoint and cubic residual. -/
theorem positiveCoefficient_cubic {f : ℝ → ℝ} {a b κ D : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) (n : ℕ) :
    ‖positiveCoefficient f (fun _ => 1) a b (n + 1) -
      (2 * Real.pi : ℂ) * (secondModeEndpoint f (deriv f) (deriv f) b n -
        secondModeEndpoint f (deriv f) (deriv f) a n)‖ ≤
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2 * ((n : ℝ) + 1 + deriv f b) ^ 3) := by
  have hρ : 0 < (n : ℝ) + 1 + deriv f b := by
    have := h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)
    positivity
  have hside : ∀ u ∈ Set.Icc a b, (n : ℝ) + 1 + deriv f b ≤ deriv f u - (-((n : ℝ) + 1)) := by
    intro u hu
    have hh := h.f_deriv_antitone hu (Set.right_mem_Icc.mpr h.lt.le) hu.2
    linarith
  have hr := norm_shifted_cubic (ν := -((n : ℝ) + 1)) h.lt.le hρ h.f_differentiable hf' hf''
    (Or.inl hside) hkneg hkb hD
  simp only [neg_mul, sub_neg_eq_add] at hr
  have hjoin (u : ℝ) (hu : u ∈ Set.Icc a b) :
      exp (2 * Real.pi * I * ((f u + ((n : ℝ) + 1) * u : ℝ) : ℂ)) /
        (2 * Real.pi * I * ((n : ℂ) + 1)) -
      (((1 / (deriv f u + ((n : ℝ) + 1)) : ℝ) : ℂ) *
        exp (2 * Real.pi * I * ((f u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) / (2 * Real.pi * I) =
      (2 * Real.pi : ℂ) * secondModeEndpoint f (deriv f) (deriv f) u n := by
    have hg : deriv f u + ((n : ℝ) + 1) ≠ 0 := by linarith [hside u hu]
    have hgc : ((deriv f u : ℝ) : ℂ) + ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast hg
    have hgc' : (n : ℂ) + 1 + ((deriv f u : ℝ) : ℂ) ≠ 0 := by simpa only [add_comm] using hgc
    have hnc : (n : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    unfold secondModeEndpoint
    push_cast
    field_simp
    ring
  rw [positiveCoefficient_eq_boundary_sub_integral h (by omega)]
  simp_rw [constant_wave_mode_neg]
  simp only [Nat.cast_add, Nat.cast_one]
  have hja := hjoin a (Set.left_mem_Icc.mpr h.lt.le)
  have hjb := hjoin b (Set.right_mem_Icc.mpr h.lt.le)
  have he : exp (2 * Real.pi * I * ((f b + ((n : ℝ) + 1) * b : ℝ) : ℂ)) /
        (2 * Real.pi * I * ((n : ℂ) + 1)) -
      exp (2 * Real.pi * I * ((f a + ((n : ℝ) + 1) * a : ℝ) : ℂ)) /
        (2 * Real.pi * I * ((n : ℂ) + 1)) -
      (∫ u in a..b, exp (2 * Real.pi * I * ((f u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) -
      (2 * Real.pi : ℂ) * (secondModeEndpoint f (deriv f) (deriv f) b n -
        secondModeEndpoint f (deriv f) (deriv f) a n) =
      -((∫ u in a..b, exp (2 * Real.pi * I * ((f u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) -
      ((((1 / (deriv f b + ((n : ℝ) + 1)) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f b + ((n : ℝ) + 1) * b : ℝ) : ℂ))) -
        (((1 / (deriv f a + ((n : ℝ) + 1)) : ℝ) : ℂ) * exp (2 * Real.pi * I * ((f a + ((n : ℝ) + 1) * a : ℝ) : ℂ)))) / (2 * Real.pi * I)) := by
    linear_combination hjb - hja
  rw [he, norm_neg]
  exact hr

end DhimanKadiriQuesadaHerrera2026


