import Dubon2026.CircleSeries

/-! # Squared norm identity for an absolutely convergent one-sided Fourier series -/

namespace Dubon2026

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- Absolute summability justifies the actual product series and its Haar integral. -/
theorem hasSum_norm_sq_fourier_nat {c : ℕ → ℂ} {g : UnitAddCircle → ℂ}
    (hc : Summable (fun n => ‖c n‖))
    (hg : ∀ z, HasSum (fun n => c n * fourier (n : ℤ) z) (g z)) :
    HasSum (fun n => ‖c n‖ ^ 2)
      (∫ z : UnitAddCircle, ‖g z‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  let F : ℕ × ℕ → UnitAddCircle → ℂ := fun p z =>
    (c p.1 * fourier (p.1 : ℤ) z) * conj (c p.2 * fourier (p.2 : ℤ) z)
  have hn (p : ℕ × ℕ) (z : UnitAddCircle) : ‖F p z‖ = ‖c p.1‖ * ‖c p.2‖ := by
    simp only [F, norm_mul, Complex.norm_conj, fourier_apply, Circle.norm_coe, mul_one]
  have hi (p : ℕ × ℕ) : Integrable (F p) AddCircle.haarAddCircle :=
    (by dsimp [F]; fun_prop : Continuous (F p)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hni : Summable (fun p : ℕ × ℕ =>
      ∫ z : UnitAddCircle, ‖F p z‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [hn]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact hc.mul_of_nonneg hc (fun n => norm_nonneg _) (fun n => norm_nonneg _)
  have hsum (z : UnitAddCircle) : HasSum (fun p : ℕ × ℕ => F p z) (g z * conj (g z)) := by
    apply HasSum.mul (f := fun n : ℕ => c n * fourier (n : ℤ) z)
      (g := fun n : ℕ => conj (c n * fourier (n : ℤ) z))
      (hg z) ((Complex.hasSum_conj').mpr (hg z))
    apply summable_mul_of_summable_norm (f := fun n : ℕ => c n * fourier (n : ℤ) z)
      (g := fun n : ℕ => conj (c n * fourier (n : ℤ) z))
    · simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hc
    · simpa only [Complex.norm_conj, norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hc
  have he (p : ℕ × ℕ) :
      (∫ z : UnitAddCircle, F p z ∂AddCircle.haarAddCircle) =
        if p.1 = p.2 then ((‖c p.1‖ ^ 2 : ℝ) : ℂ) else 0 := by
    have hf (z : UnitAddCircle) : F p z = c p.1 * conj (c p.2) *
        fourier ((p.1 : ℤ) - (p.2 : ℤ)) z := by
      simp only [F, map_mul, ← fourier_neg, sub_eq_add_neg, fourier_add]
      ring
    simp_rw [hf]
    rw [integral_const_mul, integral_circle_fourier]
    by_cases hp : p.1 = p.2
    · simp [hp, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · simp [hp, sub_eq_zero]
  have hh := hasSum_integral_of_summable_integral_norm hi hni
  simp_rw [(hsum _).tsum_eq, he] at hh
  have hd : HasSum (fun n => ((‖c n‖ ^ 2 : ℝ) : ℂ))
      (∫ z : UnitAddCircle, g z * conj (g z) ∂AddCircle.haarAddCircle) := by
    apply hh.prod_fiberwise
    intro n
    simpa only [eq_comm] using hasSum_ite_eq n ((‖c n‖ ^ 2 : ℝ) : ℂ)
  rw [show (fun z => g z * conj (g z)) = (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) by
    funext z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq], integral_complex_ofReal] at hd
  exact Complex.hasSum_ofReal.mp hd

end
end Dubon2026
