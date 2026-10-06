import DhimanKadiriQuesadaHerrera2026.CubicCoefficients

/-! # Cubic Fourier tails for actual constant-weight Poisson summation

The bounds derive every convergence input and retain the actual oscillatory
endpoint series. They do not adopt any pending source repair.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- Half-integer endpoints have unit absolute sine in the geometric tail estimate. -/
theorem abs_sin_half_integer {x : ℝ} (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) :
    |Real.sin (Real.pi * x)| = 1 := by
  obtain ⟨k, rfl⟩ := hx
  rw [show Real.pi * ((k : ℝ) + 1 / 2) = Real.pi / 2 + k * Real.pi by ring,
    Real.sin_add_int_mul_pi, Real.sin_pi_div_two, mul_one, abs_zpow]
  norm_num

/-- Removing the first positive frequency leaves a geometric endpoint tail with denominator starting at two. -/
theorem positive_tail_from_two {x y : ℝ} (hy : 0 < y) (hx : |Real.sin (Real.pi * x)| = 1) :
    ‖∑' n : ℕ, expMode x (n + 2) / (((n : ℝ) + 2) * ((n : ℝ) + 2 + y) : ℝ)‖ ≤
      1 / (2 * (2 + y)) := by
  let w : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 2) * ((n : ℝ) + 2 + y))
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have ha : Antitone w := by
    intro n m hnm
    have hh := antitone_positive_tail_weight hy (Nat.add_le_add_right hnm 1)
    simpa only [w, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hh
  have hs : Summable w := by
    have hh := (hasSum_harmonic_plus hy).summable.comp_injective (fun n m (he : n + 1 = m + 1) => by omega)
    change Summable (fun n : ℕ => 1 / ((((n + 1 : ℕ) : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + 1 + y))) at hh
    simpa only [w, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hh
  have hn : Real.sin (Real.pi * x) ≠ 0 := by intro hh; simp [hh] at hx
  have hh := norm_tsum_weighted_modes_le hw ha hs hn 1
  simp only [hx, div_one, w, Nat.cast_zero, zero_add] at hh
  convert hh using 1
  congr 1
  apply tsum_congr
  intro n
  simp only [Complex.real_smul, Nat.add_assoc, one_add_one_eq_two]
  push_cast
  ring

/-- The residual positive endpoint series at each half integer has a uniform curvature-free norm. -/
theorem second_endpoint_from_two {f p : ℝ → ℝ} {x : ℝ} (hp : 0 < p x)
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) :
    ‖∑' n : ℕ, secondModeEndpoint f p p x (n + 1)‖ ≤ 1 / (8 * Real.pi ^ 2) := by
  have hsine : |Real.sin (Real.pi * (-x))| = 1 := by
    rw [mul_neg, Real.sin_neg, abs_neg]
    exact abs_sin_half_integer hx
  have ht := positive_tail_from_two hp hsine
  have he (n : ℕ) : secondModeEndpoint f p p x (n + 1) =
      ((p x : ℂ) * exp (2 * Real.pi * I * (f x : ℂ)) / (4 * (Real.pi : ℂ) ^ 2 * I)) *
        (expMode (-x) (n + 2) / (((n : ℝ) + 2) * ((n : ℝ) + 2 + p x) : ℝ)) := by
    rw [secondModeEndpoint_eq]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
  simp_rw [he]
  rw [tsum_mul_left, norm_mul]
  have hnorm : ‖(p x : ℂ) * exp (2 * Real.pi * I * (f x : ℂ)) / (4 * (Real.pi : ℂ) ^ 2 * I)‖ =
      p x / (4 * Real.pi ^ 2) := by
    have hex : ‖exp (2 * Real.pi * I * (f x : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [norm_div, norm_mul, hex, mul_one]
    simp [Real.norm_eq_abs, abs_of_pos hp]
  rw [hnorm]
  apply (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ p x / (4 * Real.pi ^ 2))).trans
  have heq : p x / (4 * Real.pi ^ 2) * (1 / (2 * (2 + p x))) =
      (1 / (8 * Real.pi ^ 2)) * (p x / (2 + p x)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  have hr : p x / (2 + p x) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 1 / (8 * Real.pi ^ 2))

/-- The actual first positive coefficient costs at most 1/π, uniformly in the upper derivative. -/
theorem positive_coefficient_first {f : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b) :
    ‖positiveCoefficient f (fun _ => 1) a b 1‖ ≤ 1 / Real.pi := by
  have ha := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have he : partICoefficient f (fun _ => 1) a = deriv f a / Real.pi := by
    unfold partICoefficient
    simp only [deriv_const, abs_zero, zero_add, mul_one]
    field_simp
  have hb := positiveCoefficient_bound h (show 1 ≤ (1 : ℕ) from le_rfl)
  rw [he] at hb
  norm_num only [Nat.cast_one, one_mul] at hb
  apply hb.trans
  have hr : deriv f a / (1 + deriv f a) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have ht := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 1 / Real.pi)
  convert ht using 1 <;> ring


set_option maxHeartbeats 800000 in
/-- Separating the first positive frequency improves the actual infinite-tail curvature budget. -/
theorem positive_tail_cubic_split {f : ℝ → ℝ} {a b κ D : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b n‖ ≤
      3 / (2 * Real.pi) + (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (∑' n : ℕ, 1 / ((n : ℝ) + (2 + deriv f b)) ^ 3) := by
  have ha := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hb := h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)
  let C := (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2)
  let R := fun n : ℕ => positiveCoefficient f (fun _ => 1) a b (n + 2) -
    (2 * Real.pi : ℂ) * (secondModeEndpoint f (deriv f) (deriv f) b (n + 1) -
      secondModeEndpoint f (deriv f) (deriv f) a (n + 1))
  have hs := (reciprocal_cube_series_bounds (by linarith : 0 < 2 + deriv f b)).1.mul_left C
  have hbound (n : ℕ) : ‖R n‖ ≤ C * (1 / ((n : ℝ) + (2 + deriv f b)) ^ 3) := by
    have hh := positiveCoefficient_cubic h hf' hf'' hkneg hkb hD (n + 1)
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, one_add_one_eq_two] at hh
    convert hh using 1
    dsimp [C]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hr := tsum_of_norm_bounded hs.hasSum hbound
  rw [tsum_mul_left] at hr
  have hsEa : Summable (fun n : ℕ => secondModeEndpoint f (deriv f) (deriv f) a (n + 1)) :=
    (summable_secondModeEndpoint f (deriv f) (deriv f) ha).comp_injective (fun _ _ he => by omega)
  have hsEb : Summable (fun n : ℕ => secondModeEndpoint f (deriv f) (deriv f) b (n + 1)) :=
    (summable_secondModeEndpoint f (deriv f) (deriv f) hb).comp_injective (fun _ _ he => by omega)
  have hsc : Summable (fun n : ℕ => positiveCoefficient f (fun _ => 1) a b (n + 2)) :=
    (summable_positiveCoefficient h).comp_injective (fun _ _ he => by omega)
  dsimp only [R] at hr
  rw [hsc.tsum_sub ((hsEb.sub hsEa).mul_left _), tsum_mul_left, hsEb.tsum_sub hsEa] at hr
  have he : ‖(2 * Real.pi : ℂ) * ((∑' n : ℕ, secondModeEndpoint f (deriv f) (deriv f) b (n + 1)) -
      ∑' n : ℕ, secondModeEndpoint f (deriv f) (deriv f) a (n + 1))‖ ≤ 1 / (2 * Real.pi) := by
    rw [norm_mul]
    have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by simp [Real.pi_pos.le]
    rw [hn]
    apply (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
      (add_le_add (second_endpoint_from_two (f := f) hb hbh) (second_endpoint_from_two (f := f) ha hah))) Real.two_pi_pos.le).trans_eq
    field_simp
    norm_num
  have ht := (norm_add_le
    ((∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b (n + 2)) -
      (2 * Real.pi : ℂ) * ((∑' n, secondModeEndpoint f (deriv f) (deriv f) b (n + 1)) -
        ∑' n, secondModeEndpoint f (deriv f) (deriv f) a (n + 1)))
    ((2 * Real.pi : ℂ) * ((∑' n, secondModeEndpoint f (deriv f) (deriv f) b (n + 1)) -
        ∑' n, secondModeEndpoint f (deriv f) (deriv f) a (n + 1)))).trans (add_le_add hr he)
  rw [sub_add_cancel] at ht
  have hsc1 : Summable (fun n : ℕ => positiveCoefficient f (fun _ => 1) a b (n + 1)) :=
    (summable_positiveCoefficient h).comp_injective (fun _ _ he => by omega)
  rw [(summable_positiveCoefficient h).tsum_eq_zero_add]
  simp only [positiveCoefficient, Nat.cast_zero, mul_zero, div_zero, zero_add]
  change ‖∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b (n + 1)‖ ≤ _
  rw [hsc1.tsum_eq_zero_add]
  simp only [Nat.zero_add, Nat.add_assoc, one_add_one_eq_two]
  apply ((norm_add_le _ _).trans (add_le_add (positive_coefficient_first h) ht)).trans_eq
  dsimp [C]
  ring

end DhimanKadiriQuesadaHerrera2026

