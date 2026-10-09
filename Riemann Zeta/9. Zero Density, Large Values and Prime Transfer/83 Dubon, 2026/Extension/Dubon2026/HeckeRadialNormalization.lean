import Dubon2026.HeckeUnitaryScalarNormalization

/-! # Exact square-root eigenvalue of the original unnormalized Hecke trace -/

namespace Dubon2026

/-- The genuine unitary normalization is precisely the inverse of the positive square root. -/
theorem hecke_sqrt_mul_normalization {p : ℝ} (hp : 0 < p) :
    (Real.sqrt p : ℂ) * ((p ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_add hp]
  norm_num

/-- Removing the actual p^(-1/2) factor gives the exact square-root times Fourier eigenvalue. -/
theorem hecke_trace_eigen_of_normalized {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : ℝ} (hp : 0 < p) (T : Module.End ℂ V) (y : V) (eigenvalue : ℂ)
    (heigen : ((p ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) • T y = eigenvalue • y) :
    T y = ((Real.sqrt p : ℂ) * eigenvalue) • y := by
  have he := congrArg (fun z : V => (Real.sqrt p : ℂ) • z) heigen
  simpa only [smul_smul, hecke_sqrt_mul_normalization hp, one_smul] using he

end Dubon2026
