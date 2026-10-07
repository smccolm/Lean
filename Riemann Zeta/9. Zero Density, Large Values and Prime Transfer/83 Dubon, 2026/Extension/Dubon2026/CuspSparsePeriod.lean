import Dubon2026.PrincipalCoprimeProjection

/-! # Exact fractional periods forced by genuine sparse cusp expansions -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

noncomputable section

/-- The actual q-parameter at 1/d has d-th power one. -/
theorem qParam_reciprocal_pow_self (d : ℕ) [NeZero d] :
    Function.Periodic.qParam 1 (1 / (d : ℂ)) ^ d = 1 := by
  rw [← qParam_nat_mul_eq_pow,
    mul_one_div_cancel (show (d : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne d))]
  simp [Function.Periodic.qParam, Complex.exp_two_pi_mul_I]

/-- Sparse support on multiples of d forces the actual analytic function to have period 1/d. -/
theorem cusp_sparse_fractional_period {N : ℕ} {k : ℤ} (d : ℕ) [NeZero d]
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) (τ : ℍ) :
    f ((1 / (d : ℝ)) +ᵥ τ) = f τ := by
  have hs := cuspCoefficients_hasSum f ((1 / (d : ℝ)) +ᵥ τ)
  have he : (fun n => cuspCoefficients f n *
      Function.Periodic.qParam 1 (((1 / (d : ℝ)) +ᵥ τ : ℍ) : ℂ) ^ n) =
      (fun n => cuspCoefficients f n * Function.Periodic.qParam 1 τ ^ n) := by
    funext n
    by_cases hn : d ∣ n
    · obtain ⟨m, rfl⟩ := hn
      simp only [coe_vadd, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
        qParam_add, mul_pow, pow_mul, qParam_reciprocal_pow_self, one_mul]
    · rw [hf n hn, zero_mul, zero_mul]
  rw [he] at hs
  exact hs.unique (cuspCoefficients_hasSum f τ)

/-- Rescaling by the exact divisor turns the derived fractional period into period one. -/
theorem cusp_sparse_rescaling_period {N : ℕ} {k : ℤ} (d : ℕ) [NeZero d]
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) (τ : ℍ) :
    f (heckeUpperPoint d 0 ((1 : ℝ) +ᵥ τ)) = f (heckeUpperPoint d 0 τ) := by
  have he : heckeUpperPoint d 0 ((1 : ℝ) +ᵥ τ) =
      (1 / (d : ℝ)) +ᵥ heckeUpperPoint d 0 τ := by
    apply UpperHalfPlane.ext
    simp only [heckeUpperPoint, coe_mk, coe_vadd, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, Nat.cast_zero, add_zero]
    ring1
  rw [he]
  exact cusp_sparse_fractional_period d f hf _

end
end Dubon2026
