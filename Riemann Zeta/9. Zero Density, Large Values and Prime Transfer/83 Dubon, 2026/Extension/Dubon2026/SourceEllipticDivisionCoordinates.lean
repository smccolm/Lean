import Dubon2026.SourceEllipticSequenceInvariantIdentity
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction ->
reverse genus -> finite exceptional-fiber census -> elliptic cyclic-subgroup
inertia -> actual torsion cardinality -> actual point multiplication formula.
These are identities for the native division polynomials of the actual
Weierstrass equation. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. The point
multiplication formula and torsion cardinality remain to be proved. -/
namespace Dubon2026.SourceEllipticDivision
open WeierstrassCurve Polynomial
open scoped Polynomial.Bivariate
variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
noncomputable section
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])
/-- The actual invariant polynomial of the Weierstrass equation. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The doubling complement of the actual division-polynomial sequence. -/
def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

open WeierstrassCurve.Affine (polynomial polynomialX polynomialY negPolynomial)
open Dubon2026.SourceEllipticSequence

theorem C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

theorem preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = (invar W) * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

theorem preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C ((invar W) * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring

theorem φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, invarDenom]; ring

/-- The integral division-polynomial y-coordinate, valid in every characteristic. -/
def ωe (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - complEDS₂Aux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

theorem ωe_spec (n : ℤ) :
    2 * (ωe W) n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = (ψc W) n := by
  have hψ : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
  rw [ψc, complEDS₂_eq_redInvarNum_sub, reduced_invariant_identity, preΨ₄_add_ψ₂_pow_four,
    mul_assoc (C _), φ_mul_ψ, hψ, invarDenom_eq_redInvarDenom_mul, ωe, ← hψ,
    invar, b₂, b₄, ψ₂, WeierstrassCurve.Affine.polynomialY,
    WeierstrassCurve.Affine.polynomialX, WeierstrassCurve.Affine.negPolynomial]
  C_simp; ring

theorem two_mul_ωe (n : ℤ) :
    2 * (ωe W) n = (ψc W) n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ωe_spec]; abel

theorem ψc_spec (n : ℤ) : W.ψ n * (ψc W) n = W.ψ (2 * n) := normEDS_mul_complEDS₂ _ _ _ _

@[simp] theorem ωe_zero : (ωe W) 0 = 1 := by simp [ωe]

@[simp] theorem ωe_one : (ωe W) 1 = Y := by
  simp [ωe, ψ₂, ← WeierstrassCurve.Affine.Y_sub_polynomialY]

@[simp] theorem ψc_neg (n : ℤ) : (ψc W) (-n) = (ψc W) n := by simp [ψc]

end
end Dubon2026.SourceEllipticDivision
