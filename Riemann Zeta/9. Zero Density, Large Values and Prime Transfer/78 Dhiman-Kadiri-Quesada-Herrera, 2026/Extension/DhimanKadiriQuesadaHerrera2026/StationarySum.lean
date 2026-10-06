import DhimanKadiriQuesadaHerrera2026.StationaryExtended

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The actual finite family of stationary integral errors sums with its exact cardinality and endpoint gaps. -/
theorem stationary_sum_bound {f : ℝ → ℝ} {a b D ℓ : ℝ} (S : Finset ℕ) (ξ : ℕ → ℝ)
    (hℓ : 0 < ℓ)
    (hξ : ∀ ν ∈ S, ξ ν ∈ Set.Ioo a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ S, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ S, Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      (S.card : ℝ) * ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        1 / Real.pi * ∑ ν ∈ S, (1 / |deriv f a - (ν : ℝ)| + 1 / |deriv f b - (ν : ℝ)|) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (s := S) (fun ν hν =>
    stationary_phase_bound hℓ (hξ ν hν).1.1 (hξ ν hν).1.2 (hξ ν hν).2 hf hf' hf'' hcurv hD)
  apply h.trans_eq
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]

/-- The paper's interior frequency count fits inside the actual derivative range when its lower endpoint is below one. -/
theorem interior_frequency_card_le {α β : ℝ} (hα : α < 1) (hβα : α ≤ β) :
    ((Finset.Icc 1 (⌊β⌋₊ - 1)).card : ℝ) ≤ β - α := by
  have hcard : (Finset.Icc 1 (⌊β⌋₊ - 1)).card = ⌊β⌋₊ - 1 := by
    rw [Nat.card_Icc]
    omega
  rw [hcard]
  by_cases hm : 1 ≤ ⌊β⌋₊
  · have hβ : 0 ≤ β := by linarith [Nat.floor_pos.mp hm]
    have hf := Nat.floor_le hβ
    rw [Nat.cast_sub hm, Nat.cast_one]
    linarith
  · have hm0 : ⌊β⌋₊ = 0 := by omega
    rw [hm0]
    norm_num
    exact hβα

/-- The actual derivative range is bounded by interval length times the curvature upper bound. -/
theorem derivative_range_le_curvature {f : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hK : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ K) :
    deriv f a - deriv f b ≤ K * (b - a) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hf' hK (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), abs_sub_comm] at h
  exact (le_abs_self _).trans h

/-- The source interior range consumes actual stationary points and has the exact nonlinear sum coefficient. -/
theorem stationary_interior_sum_bound {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
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
        1 / Real.pi * ∑ ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1),
          (1 / |deriv f a - (ν : ℝ)| + 1 / |deriv f b - (ν : ℝ)|) := by
  have hdrop := stationary_derivative_drop hf' hcurv (Set.left_mem_Icc.mpr hab.le)
    (Set.right_mem_Icc.mpr hab.le) hab.le
  have hβα : deriv f b ≤ deriv f a := by nlinarith [mul_pos hℓ (sub_pos.mpr hab)]
  have hβ : 0 ≤ deriv f a := hαpos.le.trans hβα
  have hpoints (ν : ℕ) (hν : ν ∈ Finset.Icc 1 (⌊deriv f a⌋₊ - 1)) :
      ξ ν ∈ Set.Ioo a b ∧ deriv f (ξ ν) = (ν : ℝ) := by
    have hνbounds := Finset.mem_Icc.mp hν
    have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast hνbounds.1
    have hνM : ν < ⌊deriv f a⌋₊ := by omega
    have hνβ : (ν : ℝ) < deriv f a := (by exact_mod_cast hνM : (ν : ℝ) < (⌊deriv f a⌋₊ : ℝ)).trans_le (Nat.floor_le hβ)
    have hcc := hξ ν hν
    constructor
    · constructor
      · exact lt_of_le_of_ne hcc.1.1 (by intro he; rw [← he] at hcc; linarith [hcc.2])
      · exact lt_of_le_of_ne hcc.1.2 (by intro he; rw [he] at hcc; linarith [hcc.2])
    · exact hcc.2
  have h := stationary_sum_bound (Finset.Icc 1 (⌊deriv f a⌋₊ - 1)) ξ hℓ hpoints hf hf' hf'' hcurv hD
  apply h.trans
  apply add_le_add ?_ le_rfl
  have hcard := (interior_frequency_card_le hα hβα).trans (derivative_range_le_curvature hab.le hf' hupper)
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a (Set.left_mem_Icc.mpr hab.le))
  apply (mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤
    (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ)).trans_eq
  field_simp

end DhimanKadiriQuesadaHerrera2026

