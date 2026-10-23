import Dubon2026.SourceEllipticOddCharTwoTorsion

/-! Actual characteristic-two ordinary quotient coordinates and discriminant.
The odd summing-set equation, nonzero tangent term and x-coordinate injection
are reused from the proved actual torsion structure. The quotient-coordinate
orbit trace supplies the two-torsion coset identities. These discharge the
finite norm premises for odd quotient ellipticity, then cyclic quotient
products, inertia census and good reduction in DUB-17 / DUB-18.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
open WeierstrassCurve
noncomputable section
section Invariants

variable {F : Type*} [Field F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

include h2 ha₁ in

theorem b₂_V : V.b₂ = 1 := by
  rw [b₂, ha₁]; linear_combination 2 * V.a₂ * h2

include ha₁ ha₃ ha₄ in

theorem b₄_V : V.b₄ = 0 := by
  rw [b₄, ha₁, ha₃, ha₄]; ring

include h2 ha₃ in

theorem b₆_V : V.b₆ = 0 := by
  rw [b₆, ha₃]; linear_combination 2 * V.a₆ * h2

include h2 ha₁ ha₃ in

theorem Δ_of_a₁_one_a₃_zero : V.Δ = V.a₆ + V.a₄ ^ 2 := by
  rw [Δ, b₂, b₄, b₆, b₈, ha₁, ha₃]
  linear_combination (-216 * V.a₆ ^ 2 - 32 * V.a₄ ^ 3 + 144 * V.a₂ * V.a₄ * V.a₆
    + 8 * V.a₂ ^ 2 * V.a₄ ^ 2 - 32 * V.a₂ ^ 3 * V.a₆ - 6 * V.a₂ * V.a₆ - V.a₆
    - 24 * V.a₂ ^ 2 * V.a₆ + 4 * V.a₂ * V.a₄ ^ 2 + 36 * V.a₄ * V.a₆) * h2

include h2 ha₁ ha₃ ha₄ in

theorem Δ_V : V.Δ = V.a₆ := by
  rw [Δ_of_a₁_one_a₃_zero h2 V ha₁ ha₃, ha₄]; ring

end Invariants

section PerPoint

variable {F : Type*} [Field F] (h2 : (2 : F) = 0) (V : WeierstrassCurve F)
  (ha₁ : V.a₁ = 1) (ha₃ : V.a₃ = 0) (ha₄ : V.a₄ = 0)

include h2 ha₁ ha₃ ha₄ in

theorem veluT_V (x y : F) : veluT V x y = x := by
  rw [veluT_eq, b₂_V h2 V ha₁, b₄_V V ha₁ ha₃ ha₄]
  linear_combination (3 : F) * x ^ 2 * h2

include h2 ha₁ ha₃ ha₄ in

theorem veluU_V {x y : F} (heq : V.toAffine.Equation x y) : veluU V x y = x ^ 2 := by
  rw [veluU_eq_Ψ₂Sq_eval V heq, Ψ₂Sq, b₂_V h2 V ha₁, b₄_V V ha₁ ha₃ ha₄, b₆_V h2 V ha₃]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination (2 : F) * x ^ 3 * h2

include h2 ha₁ ha₃ ha₄ in

theorem veluW_V {x y : F} (heq : V.toAffine.Equation x y) : veluW V x y = 0 := by
  rw [veluW, veluU_V h2 V ha₁ ha₃ ha₄ heq, veluT_V h2 V ha₁ ha₃ ha₄]
  linear_combination (x : F) ^ 2 * h2

include h2 ha₁ ha₃ in

theorem veluGy_V (x y : F) : veluGy V x y = x := by
  simp only [veluGy, ha₁, ha₃]
  linear_combination (-y - x) * h2

end PerPoint


end
end Dubon2026.SourceEllipticVelu.OddDiscriminant.CharTwo
