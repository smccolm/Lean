import Dubon2026.SourceEllipticVeluTwoQuotient

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> arithmetic automorphy -> original Frobenius/inertia -> good
reduction -> reverse genus -> finite exceptional fibers -> elliptic inertia
orbits -> cyclic-quotient interpretation of modular-polynomial roots.
This step proves ellipticity of the literal degree-two Velu curve and enumerates
the three nonzero two-torsion coordinates in characteristic different from two.
The quotient group map, kernel and modular-polynomial identity remain required.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the six VeluOrderTwo discriminant
solutions and the two-torsion enumeration solution. Polynomial elimination
replaces the source's large linear-combination certificates. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R}

private theorem a₃_of_veluGy_eq_zero (hgy : veluGy W x₀ y₀ = 0) :
    W.a₃ = -(2 * y₀ + W.a₁ * x₀) := by
  simp only [veluGy] at hgy
  linear_combination -hgy

private theorem a₆_of_equation (hQ : W.toAffine.Equation x₀ y₀) :
    W.a₆ = y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
      (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hQ
  linear_combination -hQ

theorem Delta_eq_veluGx_sq_mul_velu2QuadDisc
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    W.Δ = veluGx W x₀ y₀ ^ 2 * velu2QuadDisc W x₀ := by
  simp only [WeierstrassCurve.Δ, velu2QuadDisc, veluGx, b₂, b₄, b₆, b₈]
  rw [a₆_of_equation hQ, a₃_of_veluGy_eq_zero hgy]
  ring

theorem veluQuotient2_Delta_eq
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    (veluQuotient2 W x₀ y₀).Δ = veluGx W x₀ y₀ * velu2QuadDisc W x₀ ^ 2 := by
  simp only [WeierstrassCurve.Δ, veluQuotient2, velu2QuadDisc, veluGx, b₂, b₄, b₆, b₈]
  rw [a₆_of_equation hQ, a₃_of_veluGy_eq_zero hgy]
  ring

end
end Dubon2026.SourceEllipticVelu
