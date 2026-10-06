import Dubon2026.TwistProductStrip

/-! # Boundary bounds for analytic products over finite torus grids -/

namespace Dubon2026

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

theorem norm_product_le_exp_sum_truncated_log {ι : Type*} [Fintype ι]
    (f : ι → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖∏ i, f i‖ ≤ Real.exp (∑ i, Real.log (max ‖f i‖ ε)) := by
  rw [norm_prod, Real.exp_sum]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  rw [Real.exp_log (lt_of_lt_of_le hε (le_max_right _ _))]
  exact le_max_left _ _

theorem twistProduct_real {ι : Type*} [Fintype ι] (a : ℕ → ℂ) (N : ℕ)
    (v : ι → PrimeTorus N) (σ : ℝ) :
    twistProduct a N v σ = ∏ i, bohrOnTorus a N σ (v i) := by
  have hf : primeTorusFlow N 0 = 0 := by ext p; simp [primeTorusFlow]
  simpa only [Complex.ofReal_zero, mul_zero, add_zero, hf] using twistProduct_vertical a N v σ 0

theorem grid_twistProduct_boundary_bound (a : ℕ → ℂ) (N m : ℕ) [NeZero m]
    (σ B : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ z : PrimeTorus N, (∑ j : PrimeCoordinate N → ZMod m,
      Real.log (max ‖bohrOnTorus a N σ (z + torusGridPoint N m j)‖ ε)) ≤ B)
    (z : PrimeTorus N) (s : ℂ) (hs : s.re = σ) :
    ‖twistProduct a N (fun j => z + torusGridPoint N m j) s‖ ≤ Real.exp B := by
  have he : s = (σ : ℂ) + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  calc
    _ = ‖∏ j : PrimeCoordinate N → ZMod m,
        bohrOnTorus a N σ ((z + torusGridPoint N m j) + primeTorusFlow N s.im)‖ := by
      conv_lhs => arg 1; arg 4; rw [he]
      rw [twistProduct_vertical]
    _ ≤ Real.exp (∑ j : PrimeCoordinate N → ZMod m,
        Real.log (max ‖bohrOnTorus a N σ ((z + torusGridPoint N m j) + primeTorusFlow N s.im)‖ ε)) :=
      norm_product_le_exp_sum_truncated_log _ hε
    _ ≤ Real.exp B := Real.exp_le_exp.mpr (by
      simpa only [add_assoc, add_left_comm, add_comm] using hb (z + primeTorusFlow N s.im))

theorem log_norm_twistProduct_le_three_lines {ι : Type*} [Fintype ι]
    (a : ℕ → ℂ) (N : ℕ) (v : ι → PrimeTorus N) {l u σ : ℝ} (hlu : l < u)
    (hσ : σ ∈ Icc l u) {A B : ℝ}
    (hA : ∀ s : ℂ, s.re = l → ‖twistProduct a N v s‖ ≤ Real.exp A)
    (hB : ∀ s : ℂ, s.re = u → ‖twistProduct a N v s‖ ≤ Real.exp B)
    (hne : twistProduct a N v σ ≠ 0) :
    Real.log ‖twistProduct a N v σ‖ ≤
      (1 - (σ - l) / (u - l)) * A + ((σ - l) / (u - l)) * B := by
  have h := norm_twistProduct_le_three_lines a N v hlu (s := (σ : ℂ)) (by simpa using hσ) hA hB
  have hh := Real.log_le_log (norm_pos_iff.mpr hne) h
  simp only [Complex.ofReal_re] at hh
  rw [Real.log_mul (Real.rpow_pos_of_pos (Real.exp_pos A) _).ne'
      (Real.rpow_pos_of_pos (Real.exp_pos B) _).ne',
    Real.log_rpow (Real.exp_pos A), Real.log_rpow (Real.exp_pos B), Real.log_exp, Real.log_exp] at hh
  exact hh

end

end Dubon2026
