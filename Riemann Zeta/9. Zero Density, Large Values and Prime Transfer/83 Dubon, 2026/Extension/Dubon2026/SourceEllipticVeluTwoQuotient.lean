import Dubon2026.SourceEllipticVeluQuotient

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

/-- The explicit degree-two Velu curve at the specified kernel coordinates. -/
def veluQuotient2 (x₀ y₀ : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * veluGx W x₀ y₀
  a₆ := W.a₆ - W.b₂ * veluGx W x₀ y₀ - 7 * (x₀ * veluGx W x₀ y₀)

variable (x₀ y₀ : R)

@[simp] theorem veluQuotient2_a₁ : (veluQuotient2 W x₀ y₀).a₁ = W.a₁ := rfl
@[simp] theorem veluQuotient2_a₂ : (veluQuotient2 W x₀ y₀).a₂ = W.a₂ := rfl
@[simp] theorem veluQuotient2_a₃ : (veluQuotient2 W x₀ y₀).a₃ = W.a₃ := rfl
theorem veluQuotient2_a₄ : (veluQuotient2 W x₀ y₀).a₄ = W.a₄ - 5 * veluGx W x₀ y₀ := rfl
theorem veluQuotient2_a₆ :
    (veluQuotient2 W x₀ y₀).a₆ = W.a₆ - W.b₂ * veluGx W x₀ y₀ - 7 * (x₀ * veluGx W x₀ y₀) :=
  rfl

theorem veluQuotient2_b₂ : (veluQuotient2 W x₀ y₀).b₂ = W.b₂ := by
  simp [b₂]

/-- The quadratic cofactor discriminant for the degree-two Velu curve. -/
def velu2QuadDisc (x₀ : R) : R :=
  W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄

theorem velu2QuadDisc_def (x₀ : R) :
    velu2QuadDisc W x₀ = W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄ := rfl

theorem velu2QuadDisc_eq_disc_cofactor (x₀ : R) :
    velu2QuadDisc W x₀
      = (W.b₂ + 4 * x₀) ^ 2 - 16 * (4 * x₀ ^ 2 + W.b₂ * x₀ + 2 * W.b₄) := by
  simp only [velu2QuadDisc]; ring

theorem map_velu2QuadDisc {S : Type*} [CommRing S] (f : R →+* S) (x₀ : R) :
    velu2QuadDisc (W.map f) (f x₀) = f (velu2QuadDisc W x₀) := by
  simp only [velu2QuadDisc, map_b₂, map_b₄, map_sub, map_mul, map_pow, map_ofNat]


end
end Dubon2026.SourceEllipticVelu
