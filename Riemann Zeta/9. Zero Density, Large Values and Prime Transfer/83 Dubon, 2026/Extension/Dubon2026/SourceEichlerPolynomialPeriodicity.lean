import Dubon2026.SourcePeriodPolynomialBound

/-! Periodicity of the actual Eichler integral controls its polynomial corrections.
DUB-17/18 -> modular Galois association -> original analytic H1 injectivity
-> boundedness of the corrected Eichler integral at each rational cusp.
The already constructed Fourier series is periodic at its original width.
Thus a periodic translate differing from it by a polynomial has a constant
correction, and inherits boundedness from the proved decay of that series.
-/

namespace Dubon2026
noncomputable section
open Complex Function Polynomial
open UpperHalfPlane hiding I
open scoped Real Manifold

/-- The original scalar Eichler series has the same positive real period as its Fourier parameter. -/
theorem sourceEichlerIntegral_vadd {h : ℝ} (hh : 0 < h) (n : ℕ)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    sourceEichlerIntegral h n f (h +ᵥ τ) = sourceEichlerIntegral h n f τ := by
  have he : Periodic.qParam h (h + (τ : ℂ)) = Periodic.qParam h τ := by
    unfold Periodic.qParam
    have hx : 2 * (π : ℂ) * I * ((h : ℂ) + τ) / h =
        2 * π * I * (τ : ℂ) / h + 2 * π * I := by
      field_simp [Complex.ofReal_ne_zero.mpr hh.ne']
      ring
    rw [hx, Complex.exp_periodic]
  unfold sourceEichlerIntegral
  simp only [coe_vadd, he]

/-- A polynomial difference between the actual Eichler integral and a periodic function is constant. -/
theorem sourceEichlerIntegral_polynomial_eq_const {h : ℝ} (hh : 0 < h) (n : ℕ)
    (f F : UpperHalfPlane → ℂ) (p : ℂ[X])
    (hp : ∀ τ, F τ = sourceEichlerIntegral h n f τ + p.eval (τ : ℂ))
    (hF : ∀ τ, F (h +ᵥ τ) = F τ) :
    p = Polynomial.C (p.eval I) := by
  apply sourcePolynomial_eq_const_of_upperHalfPlane_periodic p hh.ne'
  intro τ
  have ht := hF τ
  rw [hp, hp, sourceEichlerIntegral_vadd hh] at ht
  exact add_left_cancel ht

/-- A periodic polynomial correction of the actual decaying Eichler integral is bounded at infinity. -/
theorem sourceEichlerIntegral_polynomial_bounded {h : ℝ} (hh : 0 < h) (n : ℕ)
    (f F : UpperHalfPlane → ℂ) (p : ℂ[X])
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f)
    (hp : ∀ τ, F τ = sourceEichlerIntegral h (n + 1) f τ + p.eval (τ : ℂ))
    (hF : ∀ τ, F (h +ᵥ τ) = F τ) :
    IsBoundedAtImInfty F := by
  have hc := sourceEichlerIntegral_polynomial_eq_const hh (n + 1) f F p hp hF
  have hE := (isZeroAtImInfty_sourceEichlerIntegral hh hfper hfhol hfbdd n).isBoundedAtImInfty
  obtain ⟨M, A, hM⟩ := isBoundedAtImInfty_iff.mp hE
  apply isBoundedAtImInfty_iff.mpr
  refine ⟨M + ‖p.eval I‖, A, ?_⟩
  intro τ hτ
  have hv : p.eval (τ : ℂ) = p.eval I := by
    simpa only [Polynomial.eval_C] using congrArg (Polynomial.eval (τ : ℂ)) hc
  rw [hp τ, hv]
  exact (norm_add_le _ _).trans (add_le_add (hM τ hτ) le_rfl)

end
end Dubon2026
