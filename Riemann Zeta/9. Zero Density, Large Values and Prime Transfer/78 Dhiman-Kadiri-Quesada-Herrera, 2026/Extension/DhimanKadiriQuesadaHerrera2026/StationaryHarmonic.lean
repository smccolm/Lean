import DhimanKadiriQuesadaHerrera2026.StationarySum
import DhimanKadiriQuesadaHerrera2026.StationaryConstants
import DhimanKadiriQuesadaHerrera2026.WeightedIntegralSums

namespace DhimanKadiriQuesadaHerrera2026

/-- Exact forward endpoint reciprocals retain the actual fractional gap. -/
theorem stationary_reciprocal_forward (N : ℕ) {α : ℝ} (hα : α < 1) :
    (∑ ν ∈ Finset.Icc 1 N, 1 / ((ν : ℝ) - α)) =
      (Complex.digamma (((N : ℝ) + 1 - α : ℝ) : ℂ)).re -
        (Complex.digamma ((1 - α : ℝ) : ℂ)).re := by
  rw [sum_Icc_one_eq_sum_range_real]
  have h := real_digamma_add_nat (by linarith : 0 < 1 - α) N
  rw [show 1 - α + (N : ℝ) = (N : ℝ) + 1 - α by ring] at h
  rw [h, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  congr 1
  ring

/-- Reflection gives the exact opposite endpoint sum, including a nonintegral upper endpoint. -/
theorem stationary_reciprocal_backward (N : ℕ) {β : ℝ} (hβ : (N : ℝ) < β) :
    (∑ ν ∈ Finset.Icc 1 N, 1 / (β - (ν : ℝ))) =
      (Complex.digamma (β : ℂ)).re -
        (Complex.digamma ((β - (N : ℝ) : ℝ) : ℂ)).re := by
  rw [sum_Icc_one_eq_sum_range_real]
  have h := real_digamma_add_nat (by linarith : 0 < β - (N : ℝ)) N
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_left, ← Finset.sum_range_reflect (fun n : ℕ => 1 / (β - (N : ℝ) + (n : ℝ))) N]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
  rw [show N - 1 - n = N - (n + 1) by omega, Nat.cast_sub hnN]
  push_cast
  congr 1
  ring

/-- Both absolute endpoint gaps evaluate to an exact digamma difference. -/
theorem stationary_reciprocal_sum_eq (N : ℕ) {α β : ℝ}
    (hα : α < 1) (hβ : (N : ℝ) < β) :
    (∑ ν ∈ Finset.Icc 1 N, (1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)|)) =
      (Complex.digamma (β : ℂ)).re - (Complex.digamma ((β - (N : ℝ) : ℝ) : ℂ)).re +
        (Complex.digamma (((N : ℝ) + 1 - α : ℝ) : ℂ)).re -
          (Complex.digamma ((1 - α : ℝ) : ℂ)).re := by
  have he (ν : ℕ) (hν : ν ∈ Finset.Icc 1 N) :
      1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)| = 1 / (β - (ν : ℝ)) + 1 / ((ν : ℝ) - α) := by
    have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast (Finset.mem_Icc.mp hν).1
    have hνN : (ν : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hν).2
    rw [abs_of_pos (by linarith : 0 < β - (ν : ℝ)), abs_of_neg (by linarith : α - (ν : ℝ) < 0), neg_sub]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib,
    stationary_reciprocal_forward N hα, stationary_reciprocal_backward N hβ]
  ring

/-- The half-integer reciprocal sum has its exact digamma value below a logarithmic majorant. -/
theorem half_integer_reciprocal_log_bound (N : ℕ) :
    (∑ ν ∈ Finset.Icc 1 N, 1 / ((ν : ℝ) - 1 / 2)) ≤
      Real.log ((N : ℝ) + 1 / 2) - (Complex.digamma (1 / 2 : ℂ)).re := by
  rw [stationary_reciprocal_forward N (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num only [show (N : ℝ) + 1 - 1 / 2 = (N : ℝ) + 1 / 2 by ring,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have h := (real_digamma_bounds (by positivity : 0 < (N : ℝ) + 1 / 2)).2
  linarith [show (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1 / 2)) by positivity]

/-- A valid separated range gives the printed logarithmic coefficient and certified decimal. -/
theorem stationary_reciprocal_log_bound (N : ℕ) {α β : ℝ}
    (hα : α ≤ 1 / 2) (hβ : (N : ℝ) + 1 ≤ β) :
    1 / Real.pi * (∑ ν ∈ Finset.Icc 1 N,
      (1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)|)) ≤
        2 / Real.pi * Real.log (β - α) + 1.251 := by
  have hpt (ν : ℕ) (hν : ν ∈ Finset.Icc 1 N) :
      1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)| ≤
        1 / ((N : ℝ) + 1 / 2 - ν) + 1 / ((ν : ℝ) - 1 / 2) := by
    have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast (Finset.mem_Icc.mp hν).1
    have hνN : (ν : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hν).2
    rw [abs_of_pos (by linarith : 0 < β - (ν : ℝ)), abs_of_neg (by linarith : α - (ν : ℝ) < 0), neg_sub]
    apply add_le_add
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hb : (∑ ν ∈ Finset.Icc 1 N, 1 / ((N : ℝ) + 1 / 2 - ν)) ≤
      Real.log ((N : ℝ) + 1 / 2) - (Complex.digamma (1 / 2 : ℂ)).re := by
    rw [half_integer_reciprocal_sum]
    have h := (real_digamma_bounds (by positivity : 0 < (N : ℝ) + 1 / 2)).2
    linarith [show (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1 / 2)) by positivity]
  have hf := half_integer_reciprocal_log_bound N
  have hs := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib] at hs
  have hlog := Real.log_le_log (by positivity : 0 < (N : ℝ) + 1 / 2)
    (by linarith : (N : ℝ) + 1 / 2 ≤ β - α)
  have ht : (∑ ν ∈ Finset.Icc 1 N,
      (1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)|)) ≤
        2 * (Real.log (β - α) - (Complex.digamma (1 / 2 : ℂ)).re) := by
    rw [Finset.sum_add_distrib]
    linarith
  apply (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 1 / Real.pi)).trans
  rw [real_digamma_half]
  calc
    _ = 2 / Real.pi * Real.log (β - α) +
        2 / Real.pi * (Real.eulerMascheroniConstant + 2 * Real.log 2) := by ring
    _ ≤ _ := add_le_add le_rfl stationary_digamma_constant_le

/-- The paper's interior frequency set has the logarithmic bound when the lower derivative is at most one half and the upper derivative is at least one. -/
theorem stationary_interior_reciprocal_log {α β : ℝ} (hα : α ≤ 1 / 2) (hβ : 1 ≤ β) :
    1 / Real.pi * (∑ ν ∈ Finset.Icc 1 (⌊β⌋₊ - 1),
      (1 / |β - (ν : ℝ)| + 1 / |α - (ν : ℝ)|)) ≤
        2 / Real.pi * Real.log (β - α) + 1.251 := by
  have hm : 1 ≤ ⌊β⌋₊ := Nat.floor_pos.mpr hβ
  apply stationary_reciprocal_log_bound _ hα
  rw [Nat.cast_sub hm, Nat.cast_one, sub_add_cancel]
  exact Nat.floor_le (by linarith)

/-- The actual interior stationary sum has an exact digamma error for the full printed lower-derivative range. -/
theorem stationary_interior_digamma_bound {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hξ : ∀ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        1 / Real.pi * (
          (Complex.digamma ((deriv f a : ℝ) : ℂ)).re -
            (Complex.digamma ((deriv f a - (⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) : ℂ)).re +
          (Complex.digamma (((⌊deriv f a⌋₊ - 1 : ℕ) + 1 - deriv f b : ℝ) : ℂ)).re -
            (Complex.digamma ((1 - deriv f b : ℝ) : ℂ)).re) := by
  have hdrop := stationary_derivative_drop hf' hcurv (Set.left_mem_Icc.mpr hab.le)
    (Set.right_mem_Icc.mpr hab.le) hab.le
  have hβpos : 0 < deriv f a := by nlinarith [mul_pos hℓ (sub_pos.mpr hab)]
  have hN : ((⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) < deriv f a := by
    by_cases hm : 1 ≤ ⌊deriv f a⌋₊
    · rw [Nat.cast_sub hm, Nat.cast_one]
      linarith [Nat.floor_le hβpos.le]
    · have hm0 : ⌊deriv f a⌋₊ = 0 := by omega
      simpa [hm0] using hβpos
  have h := stationary_interior_sum_bound ξ hab hℓ hαpos hα hξ hf hf' hf'' hcurv hupper hD
  rwa [stationary_reciprocal_sum_eq _ hα hN] at h

/-- The exact logarithmic stationary sum estimate on the explicitly separated derivative subdomain. -/
theorem stationary_interior_log_bound {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b ≤ 1 / 2) (hβ : 1 ≤ deriv f a)
    (hξ : ∀ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        (2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251) := by
  have h := stationary_interior_sum_bound ξ hab hℓ hαpos (by linarith) hξ hf hf' hf'' hcurv hupper hD
  exact h.trans (add_le_add le_rfl (stationary_interior_reciprocal_log hα hβ))

end DhimanKadiriQuesadaHerrera2026
