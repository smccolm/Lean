import DhimanKadiriQuesadaHerrera2026.CubicCoefficients
import DhimanKadiriQuesadaHerrera2026.SecondTailSharp

/-! # Cubic Fourier tails for actual constant-weight Poisson summation

The bounds derive every convergence input and retain the actual oscillatory
endpoint series. They are independent of the general Part-II source repairs.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- The full actual upper-frequency tail has a cubic summable error and cancellation-preserving endpoints. -/
theorem negative_tail_cubic {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : deriv f a < (M : ℝ) + 1) :
    ‖∑' n : ℕ, negativeCoefficient f (fun _ => 1) a b (n + M + 1)‖ ≤
      deriv f b / (2 * Real.pi) * ‖negativeTail M b (deriv f b)‖ +
      deriv f a / (2 * Real.pi) * ‖negativeTail M a (deriv f a)‖ +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (∑' n : ℕ, 1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) := by
  have ha := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hb := h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)
  have hMb : deriv f b < (M : ℝ) + 1 :=
    (h.f_deriv_antitone (Set.left_mem_Icc.mpr h.lt.le) (Set.right_mem_Icc.mpr h.lt.le) h.lt.le).trans_lt hM
  let C := (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2)
  let R := fun n : ℕ => negativeCoefficient f (fun _ => 1) a b (n + M + 1) -
    (2 * Real.pi : ℂ) * (upperModeEndpoint f (deriv f) (deriv f) b M n -
      upperModeEndpoint f (deriv f) (deriv f) a M n)
  have hs := (reciprocal_cube_series_bounds (by linarith : 0 < (M : ℝ) + 1 - deriv f a)).1.mul_left C
  have hbound (n : ℕ) : ‖R n‖ ≤ C * (1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) := by
    have hh := negativeCoefficient_cubic h hf' hf'' hkneg hkb hD hM n
    convert hh using 1
    dsimp [C]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hr := tsum_of_norm_bounded hs.hasSum hbound
  rw [tsum_mul_left] at hr
  have hsEa := summable_upperModeEndpoint f (deriv f) (deriv f) ha hM
  have hsEb := summable_upperModeEndpoint f (deriv f) (deriv f) hb hMb
  have hsc : Summable (fun n : ℕ => negativeCoefficient f (fun _ => 1) a b (n + M + 1)) :=
    (summable_negativeCoefficient h).comp_injective (fun _ _ he => by omega)
  dsimp only [R] at hr
  rw [hsc.tsum_sub ((hsEb.sub hsEa).mul_left _), tsum_mul_left, hsEb.tsum_sub hsEa] at hr
  have ht := (norm_add_le
    ((∑' n : ℕ, negativeCoefficient f (fun _ => 1) a b (n + M + 1)) -
      (2 * Real.pi : ℂ) * ((∑' n, upperModeEndpoint f (deriv f) (deriv f) b M n) -
        ∑' n, upperModeEndpoint f (deriv f) (deriv f) a M n))
    ((2 * Real.pi : ℂ) * ((∑' n, upperModeEndpoint f (deriv f) (deriv f) b M n) -
        ∑' n, upperModeEndpoint f (deriv f) (deriv f) a M n))).trans (add_le_add hr le_rfl)
  rw [sub_add_cancel, norm_mul] at ht
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by simp [Real.pi_pos.le]
  rw [hn] at ht
  have he := mul_le_mul_of_nonneg_left (norm_sub_le
    (∑' n, upperModeEndpoint f (deriv f) (deriv f) b M n)
    (∑' n, upperModeEndpoint f (deriv f) (deriv f) a M n)) Real.two_pi_pos.le
  rw [norm_tsum_upperModeEndpoint f (deriv f) (deriv f) hb hMb,
    norm_tsum_upperModeEndpoint f (deriv f) (deriv f) ha hM,
    abs_of_pos hb, abs_of_pos ha] at he
  apply ht.trans
  apply (add_le_add le_rfl he).trans_eq
  dsimp [C]
  field_simp
  ring

/-- The full actual positive-frequency tail has a cubic summable error and cancellation-preserving endpoints. -/
theorem positive_tail_cubic {f : ℝ → ℝ} {a b κ D : ℝ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    :
    ‖∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b (n + 1)‖ ≤
      deriv f b / (2 * Real.pi) * ‖positiveTail (-b) (deriv f b)‖ +
      deriv f a / (2 * Real.pi) * ‖positiveTail (-a) (deriv f a)‖ +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (∑' n : ℕ, 1 / ((n : ℝ) + (1 + deriv f b)) ^ 3) := by
  have ha := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hb := h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)
  let C := (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2)
  let R := fun n : ℕ => positiveCoefficient f (fun _ => 1) a b (n + 1) -
    (2 * Real.pi : ℂ) * (secondModeEndpoint f (deriv f) (deriv f) b n -
      secondModeEndpoint f (deriv f) (deriv f) a n)
  have hs := (reciprocal_cube_series_bounds (by linarith : 0 < 1 + deriv f b)).1.mul_left C
  have hbound (n : ℕ) : ‖R n‖ ≤ C * (1 / ((n : ℝ) + (1 + deriv f b)) ^ 3) := by
    have hh := positiveCoefficient_cubic h hf' hf'' hkneg hkb hD n
    convert hh using 1
    dsimp [C]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hr := tsum_of_norm_bounded hs.hasSum hbound
  rw [tsum_mul_left] at hr
  have hsEa := summable_secondModeEndpoint f (deriv f) (deriv f) ha
  have hsEb := summable_secondModeEndpoint f (deriv f) (deriv f) hb
  have hsc : Summable (fun n : ℕ => positiveCoefficient f (fun _ => 1) a b (n + 1)) :=
    (summable_positiveCoefficient h).comp_injective (fun _ _ he => by omega)
  dsimp only [R] at hr
  rw [hsc.tsum_sub ((hsEb.sub hsEa).mul_left _), tsum_mul_left, hsEb.tsum_sub hsEa] at hr
  have ht := (norm_add_le
    ((∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b (n + 1)) -
      (2 * Real.pi : ℂ) * ((∑' n, secondModeEndpoint f (deriv f) (deriv f) b n) -
        ∑' n, secondModeEndpoint f (deriv f) (deriv f) a n))
    ((2 * Real.pi : ℂ) * ((∑' n, secondModeEndpoint f (deriv f) (deriv f) b n) -
        ∑' n, secondModeEndpoint f (deriv f) (deriv f) a n))).trans (add_le_add hr le_rfl)
  rw [sub_add_cancel, norm_mul] at ht
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by simp [Real.pi_pos.le]
  rw [hn] at ht
  have he := mul_le_mul_of_nonneg_left (norm_sub_le
    (∑' n, secondModeEndpoint f (deriv f) (deriv f) b n)
    (∑' n, secondModeEndpoint f (deriv f) (deriv f) a n)) Real.two_pi_pos.le
  rw [norm_tsum_secondModeEndpoint f (deriv f) (deriv f) hb,
    norm_tsum_secondModeEndpoint f (deriv f) (deriv f) ha,
    abs_of_pos hb, abs_of_pos ha] at he
  apply ht.trans
  apply (add_le_add le_rfl he).trans_eq
  dsimp [C]
  field_simp
  ring


set_option maxHeartbeats 800000 in
/-- Actual half-integer Poisson summation with cubic tails, using only the source curvature and third-derivative bounds. -/
theorem constant_poisson_cubic_series {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : 1 ≤ M) (hδ : 1 / 2 ≤ (M : ℝ) + 1 - deriv f a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, exp (2 * Real.pi * I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        exp (2 * Real.pi * I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / (M : ℝ)) / Real.pi + 1 / 2 + Real.log 2 / Real.pi +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        ((∑' n : ℕ, 1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) +
          ∑' n : ℕ, 1 / ((n : ℝ) + (1 + deriv f b)) ^ 3) := by
  have ha := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hb := h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)
  have hba := h.f_deriv_antitone (Set.left_mem_Icc.mpr h.lt.le) (Set.right_mem_Icc.mpr h.lt.le) h.lt.le
  have hδb : 1 / 2 ≤ (M : ℝ) + 1 - deriv f b := by linarith
  have hmpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hn := negative_tail_cubic h hf' hf'' hkneg hkb hD (by linarith : deriv f a < (M : ℝ) + 1)
  have hp := positive_tail_cubic h hf' hf'' hkneg hkb hD
  have hps : (∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b n) =
      ∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b (n + 1) := by
    rw [(summable_positiveCoefficient h).tsum_eq_zero_add]
    simp only [positiveCoefficient, Nat.cast_zero, mul_zero, div_zero, zero_add]
  rw [← hps] at hp
  have hea := norm_poissonHeadBoundary_half_integer_le (f := f) (g := fun _ => 1) hah (by norm_num) hmpos
  have heb := norm_poissonHeadBoundary_half_integer_le (f := f) (g := fun _ => 1) hbh (by norm_num) hmpos
  simp only [Nat.floor_natCast] at hea heb
  have hea' : deriv f a / (2 * Real.pi) * (‖negativeTail M a (deriv f a)‖ + ‖positiveTail (-a) (deriv f a)‖) ≤
      (Real.pi / 2 + Real.log 2) / (2 * Real.pi) := by
    have hh := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_sharp hah ha hδ) (div_nonneg ha.le Real.two_pi_pos.le)
    convert hh using 1
    field_simp
  have heb' : deriv f b / (2 * Real.pi) * (‖negativeTail M b (deriv f b)‖ + ‖positiveTail (-b) (deriv f b)‖) ≤
      (Real.pi / 2 + Real.log 2) / (2 * Real.pi) := by
    have hh := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_sharp hbh hb hδb) (div_nonneg hb.le Real.two_pi_pos.le)
    convert hh using 1
    field_simp
  have hzero : poissonBoundary f (fun _ => 1) a b = 0 := by
    obtain ⟨k, rfl⟩ := hah
    obtain ⟨l, rfl⟩ := hbh
    exact poissonBoundary_half_integer f (fun _ => 1) k l
  have htri (A B T P : ℂ) : ‖A - B + T - P‖ ≤ ‖A‖ + ‖B‖ + ‖T‖ + ‖P‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  have ht := htri (poissonHeadBoundary f (fun _ => 1) b M) (poissonHeadBoundary f (fun _ => 1) a M)
    (∑' n : ℕ, negativeCoefficient f (fun _ => 1) a b (n + M + 1))
    (∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b n)
  rw [← add_zero (_ - _ + _ - _), ← hzero, ← weighted_sum_eq_poissonMain_add_remainder h,
    poissonMain_eq_source] at ht
  simp only [weightedWave, Complex.ofReal_one, one_mul] at ht
  apply ht.trans
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hea heb hea' heb' hn hp ⊢
  nlinarith only [hea, heb, hea', heb', hn, hp, mul_inv_cancel₀ Real.pi_ne_zero]

/-- The actual cubic Poisson remainder has a fully explicit reciprocal envelope. -/
theorem constant_poisson_cubic {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : 1 ≤ M) (hδ : 1 / 2 ≤ (M : ℝ) + 1 - deriv f a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, exp (2 * Real.pi * I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        exp (2 * Real.pi * I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / (M : ℝ)) / Real.pi + 1 / 2 + Real.log 2 / Real.pi +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        (1 / ((M : ℝ) + 1 - deriv f a) ^ 3 +
          1 / ((M : ℝ) + 2 - deriv f a) ^ 3 + 1 / (2 * ((M : ℝ) + 2 - deriv f a) ^ 2) +
          1 / (1 + deriv f b) ^ 3 + 1 / (2 + deriv f b) ^ 3 + 1 / (2 * (2 + deriv f b) ^ 2)) := by
  have ha := Set.left_mem_Icc.mpr h.lt.le
  have hκ : 0 ≤ κ := (abs_nonneg _).trans (hkb a ha)
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a ha)
  have hL : 0 ≤ b - a := sub_nonneg.mpr h.lt.le
  have hC : 0 ≤ (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) := by positivity
  apply (constant_poisson_cubic_series h hf' hf'' hkneg hkb hD hM hδ hah hbh).trans
  apply add_le_add le_rfl
  have hn := (reciprocal_cube_series_sharp (by linarith : 0 < (M : ℝ) + 1 - deriv f a)).2
  have hp := (reciprocal_cube_series_sharp (by linarith [h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)] : 0 < 1 + deriv f b)).2
  apply mul_le_mul_of_nonneg_left _ hC
  convert add_le_add hn hp using 1
  ring

end DhimanKadiriQuesadaHerrera2026

