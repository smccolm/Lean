import Dubon2026.SourceFrickeCyclotomicField

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 character realization -> Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> cyclotomic
Fricke expansions. The actual torsion expansion is regrouped by its
finite exponent fibers and identified with the native q-expansion.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
No external theorem module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

/-- The explicit normalized Fourier expression for the actual torsion Weierstrass value. -/
def wpNormSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
    ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ

lemma wpTorsionSeries_eq (N a₁ a₂ : ℕ) (τ : ℂ) :
    wpTorsionSeries N a₁ a₂ τ = (2 * π * I) ^ 2 * wpNormSeries N a₁ a₂ τ := rfl

/-- The normalized actual Weierstrass value with natural-number torsion coordinates. -/
def wpNorm (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ := ((2 * π * I) ^ 2)⁻¹ * wpTorsion N a₁ a₂ τ

lemma wpNorm_eq {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    wpNorm N a₁ a₂ τ = wpNormSeries N a₁ a₂ τ := by
  rw [wpNorm, wpTorsion_eq_wpTorsionSeries ha₁ ha₂ h0, wpTorsionSeries_eq,
    inv_mul_cancel_left₀ (pow_ne_zero 2 Complex.two_pi_I_ne_zero)]

lemma qN_add_natCast (N : ℕ) (hN : N ≠ 0) (τ : ℂ) : qN N (τ + N) = qN N τ := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [qN, qN, mul_add, add_div, Complex.exp_add, mul_div_cancel_right₀ _ this,
    Complex.exp_two_pi_mul_I, mul_one]

lemma wpTail_add_natCast {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) :
    wpTail N a₁ a₂ p (τ + N) = wpTail N a₁ a₂ p τ := by
  simp only [wpTail, qN_add_natCast N hN]

lemma wpNormSeries_add_natCast {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (τ : ℂ) :
    wpNormSeries N a₁ a₂ (τ + N) = wpNormSeries N a₁ a₂ τ := by
  simp only [wpNormSeries, qN_add_natCast N hN, wpTail_add_natCast hN]

theorem periodic_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    Function.Periodic (wpNorm N a₁ a₂ ∘ ofComplex) N := by
  have hN : N ≠ 0 := by omega
  intro τ
  simp only [Function.comp_apply]
  rcases le_or_gt τ.im 0 with hτ | hτ
  · rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hτ) hτ]
  · have hτ' : 0 < (τ + N).im := by simpa using hτ
    rw [ofComplex_apply_of_im_pos hτ', ofComplex_apply_of_im_pos hτ, wpNorm_eq ha₁ ha₂ h0,
      wpNorm_eq ha₁ ha₂ h0]
    push_cast
    exact wpNormSeries_add_natCast hN a₁ a₂ τ

theorem mdifferentiable_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNorm N a₁ a₂) :=
  (mdifferentiable_wpTorsion ha₁ ha₂ h0).const_smul ((2 * π * I) ^ 2)⁻¹


end
end Dubon2026.SourceFricke
