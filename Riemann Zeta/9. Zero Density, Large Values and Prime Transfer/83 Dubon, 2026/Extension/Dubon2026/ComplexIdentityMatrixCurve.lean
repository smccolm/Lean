import Dubon2026.ComplexTracelessProjection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Actual invertible complex matrix curves with every original tangent -/

namespace Dubon2026

noncomputable section
open Filter
open scoped Topology

/-- The determinant of the literal I+tA curve has its exact original trace derivative. -/
theorem complexIdentityMatrixCurve_det_hasDerivAt (a : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun t : ℂ => Matrix.det (1 + t • a)) (Matrix.trace a) 0 := by
  have h₀₀ := ((hasDerivAt_id (0 : ℂ)).mul_const (a 0 0)).const_add 1
  have h₁₁ := ((hasDerivAt_id (0 : ℂ)).mul_const (a 1 1)).const_add 1
  have h₀₁ := (hasDerivAt_id (0 : ℂ)).mul_const (a 0 1)
  have h₁₀ := (hasDerivAt_id (0 : ℂ)).mul_const (a 1 0)
  simpa [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.trace, Fin.sum_univ_two, add_comm] using (h₀₀.mul h₁₁).sub (h₀₁.mul h₁₀)

/-- The original I+tA matrix is invertible throughout a genuine neighborhood of zero. -/
theorem complexIdentityMatrixCurve_det_eventually_ne_zero (a : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ᶠ t : ℂ in 𝓝 0, Matrix.det (1 + t • a) ≠ 0 := by
  exact (complexIdentityMatrixCurve_det_hasDerivAt a).continuousAt.eventually
    (isOpen_ne.mem_nhds (by simp))

/-- The actual invertible matrix curve agrees with I+tA on its original invertible neighborhood. -/
def complexIdentityGLCurve (a : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  if h : Matrix.det (1 + t • a) ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + t • a) h else 1

/-- The genuine general-linear-group curve retains its literal original matrix entries near zero. -/
theorem complexIdentityGLCurve_eventually (a : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ᶠ t : ℂ in 𝓝 0, (complexIdentityGLCurve a t : Matrix (Fin 2) (Fin 2) ℂ) = 1 + t • a := by
  filter_upwards [complexIdentityMatrixCurve_det_eventually_ne_zero a] with t ht
  simp [complexIdentityGLCurve, ht, Matrix.GeneralLinearGroup.mkOfDetNeZero]

end
end Dubon2026
