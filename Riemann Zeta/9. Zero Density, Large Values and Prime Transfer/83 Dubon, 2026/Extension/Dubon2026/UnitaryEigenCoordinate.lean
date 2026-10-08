import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Exact dual eigen-coordinates of a genuine unitary operator -/

namespace Dubon2026

open scoped ComplexConjugate

/-- Under the actual unitary action, the coordinate along a unit-modulus eigenvector transforms by that same eigenvalue. -/
theorem unitary_eigen_coordinate {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : Module.End ℂ V) (hT : ∀ v w, inner ℂ (T v) (T w) = inner ℂ v w)
    (b : V) (μ : ℂ) (hμ : ‖μ‖ = 1) (hb : T b = μ • b) (v : V) :
    inner ℂ b (T v) = μ * inner ℂ b v := by
  have hi := hT b v
  rw [hb, inner_smul_left] at hi
  have he := congrArg (fun z : ℂ => μ * z) hi
  have hc : μ * conj μ = 1 := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]
  simpa only [← mul_assoc, hc, one_mul] using he

end Dubon2026
