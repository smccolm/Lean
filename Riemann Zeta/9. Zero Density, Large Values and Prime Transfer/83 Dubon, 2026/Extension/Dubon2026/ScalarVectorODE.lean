import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The actual vector solution of a scalar linear differential equation -/

namespace Dubon2026

noncomputable section

/-- A genuine norm-differentiable vector orbit with scalar infinitesimal is its original exponential orbit. -/
theorem scalarVectorODE_solution {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (F : ℝ → V) (a : ℂ) (hF : ∀ t, HasDerivAt F (a • F t) t) (t : ℝ) :
    F t = Complex.exp ((t : ℂ) * a) • F 0 := by
  let G : ℝ → V := fun u => Complex.exp ((u : ℂ) * (-a)) • F u
  have hG (u : ℝ) : HasDerivAt G 0 u := by
    have he := (((hasDerivAt_id u).ofReal_comp).mul_const (-a)).cexp
    convert he.smul (hF u) using 1
    simp only [id_eq, Complex.ofReal_one, one_mul, smul_smul, ← add_smul]
    have hz : Complex.exp ((u : ℂ) * -a) * a + Complex.exp ((u : ℂ) * -a) * -a = 0 := by ring
    rw [hz, zero_smul]
  have hc : G t = F 0 := by
    have h := is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt)
      (fun u => (hG u).deriv) t 0
    simpa [G] using h
  have he : Complex.exp ((t : ℂ) * a) • G t = F t := by
    dsimp only [G]
    rw [smul_smul, ← Complex.exp_add]
    simp
  exact he.symm.trans (congrArg (fun v => Complex.exp ((t : ℂ) * a) • v) hc)

end
end Dubon2026
