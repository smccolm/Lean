import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> elliptic inertia orbits
-> actual cyclic-quotient interpretation of modular-polynomial roots
-> actual Velu quotients and their specialization. These are the literal
coefficient formulas and their proved identities, including base change
under injectivity on the finite coordinate set. Ellipticity of the quotient,
the quotient homomorphism, its kernel and the modular-polynomial identity
still require proofs. No such conclusions are packaged as assumptions here.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Definitions/Def_WeierstrassCurve_Velu.lean,
Def_WeierstrassCurve_VeluOrderTwo.lean and
P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j.lean. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The x derivative term in the actual Velu coefficient formulas. -/
def veluGx (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

/-- The y derivative term in the actual Velu coefficient formulas. -/
def veluGy (x y : R) : R := -(2 * y + W.a₁ * x + W.a₃)

/-- The actual Velu T coefficient contribution. -/
def veluT (x y : R) : R := 2 * veluGx W x y - W.a₁ * veluGy W x y

/-- The actual Velu U coefficient contribution. -/
def veluU (x y : R) : R := veluGy W x y ^ 2

/-- The actual Velu W coefficient contribution. -/
def veluW (x y : R) : R := veluU W x y + x * veluT W x y

theorem veluT_eq (x y : R) : veluT W x y = 6 * x ^ 2 + W.b₂ * x + W.b₄ := by
  simp only [veluT, veluGx, veluGy, b₂, b₄]; ring

theorem veluU_eq_Ψ₂Sq_eval {x y : R} (h : W.toAffine.Equation x y) :
    veluU W x y = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [veluU, veluGy, Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * h

theorem veluGy_negY (x y : R) : veluGy W x (W.toAffine.negY x y) = -veluGy W x y := by
  simp only [veluGy, WeierstrassCurve.Affine.negY]; ring

theorem veluT_negY (x y : R) : veluT W x (W.toAffine.negY x y) = veluT W x y := by
  simp only [veluT_eq]

theorem veluU_negY (x y : R) : veluU W x (W.toAffine.negY x y) = veluU W x y := by
  simp only [veluU, veluGy, WeierstrassCurve.Affine.negY]; ring

theorem veluW_negY (x y : R) : veluW W x (W.toAffine.negY x y) = veluW W x y := by
  simp only [veluW, veluU_negY, veluT_negY]

theorem veluGy_eq_zero_of_negY_eq {x y : R} (h : W.toAffine.negY x y = y) :
    veluGy W x y = 0 := by
  have : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have := h
    simp only [WeierstrassCurve.Affine.negY] at this
    linear_combination -this
  simp [veluGy, this]


end
end Dubon2026.SourceEllipticVelu
