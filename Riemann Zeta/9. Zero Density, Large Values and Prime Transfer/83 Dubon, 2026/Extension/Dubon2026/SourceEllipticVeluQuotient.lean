import Dubon2026.SourceEllipticVeluCoefficients

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

variable (S : Finset (R × R))

/-- Sum of the actual T contributions over the specified finite coordinate set. -/
def veluTSum : R := ∑ P ∈ S, veluT W P.1 P.2

/-- Sum of the actual W contributions over the specified finite coordinate set. -/
def veluWSum : R := ∑ P ∈ S, veluW W P.1 P.2

@[simp] theorem veluTSum_empty : veluTSum W ∅ = 0 := by simp [veluTSum]

@[simp] theorem veluWSum_empty : veluWSum W ∅ = 0 := by simp [veluWSum]

/-- The explicit Weierstrass curve given by the actual Velu coefficient sums. -/
def veluQuotient : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * veluTSum W S
  a₆ := W.a₆ - W.b₂ * veluTSum W S - 7 * veluWSum W S

@[simp] theorem veluQuotient_a₁ : (veluQuotient W S).a₁ = W.a₁ := rfl
@[simp] theorem veluQuotient_a₂ : (veluQuotient W S).a₂ = W.a₂ := rfl
@[simp] theorem veluQuotient_a₃ : (veluQuotient W S).a₃ = W.a₃ := rfl
theorem veluQuotient_a₄ : (veluQuotient W S).a₄ = W.a₄ - 5 * veluTSum W S := rfl
theorem veluQuotient_a₆ :
    (veluQuotient W S).a₆ = W.a₆ - W.b₂ * veluTSum W S - 7 * veluWSum W S := rfl

@[simp] theorem veluQuotient_empty : veluQuotient W ∅ = W := by
  ext <;> simp [veluQuotient]

theorem veluQuotient_b₂ : (veluQuotient W S).b₂ = W.b₂ := by
  simp [b₂]

theorem veluQuotient_b₄ : (veluQuotient W S).b₄ = W.b₄ - 10 * veluTSum W S := by
  simp only [b₄, veluQuotient_a₃, veluQuotient_a₁, veluQuotient_a₄]; ring

theorem veluQuotient_b₆ :
    (veluQuotient W S).b₆ = W.b₆ - 4 * W.b₂ * veluTSum W S - 28 * veluWSum W S := by
  simp only [b₆, b₂, veluQuotient_a₃, veluQuotient_a₆]; ring

theorem veluQuotient_b₈ :
    (veluQuotient W S).b₈ = W.b₈ + (5 * W.b₄ - W.b₂ ^ 2) * veluTSum W S
      - 7 * W.b₂ * veluWSum W S - 25 * veluTSum W S ^ 2 := by
  simp only [b₈, b₂, b₄, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆]
  ring


end
end Dubon2026.SourceEllipticVelu
