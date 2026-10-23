import Dubon2026.SourceEllipticVeluTwoSecantCleared

/-! Cleared degree-two Velu identities for the actual secant and tangent
group-law cases. These discharge coordinate identities needed by the quotient
homomorphism, cyclic-quotient modular-polynomial roots and elliptic inertia
census on the good-reduction chain for DUB-17 / DUB-18.
Adapted statements from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the three cleared-identity solutions.
The two y identities use cubic root relations instead of large expanded
certificates. All proofs use the unchanged default proof limits. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
private theorem velu2TangentAddX_assemble {R : Type*} [CommRing R] {A M C D t u : R}
    (h1 : A * u = t ^ 2) (h2 : C = D ^ 2) (h3 : M = t ^ 2 * u + 2 * D ^ 2) :
    A * M * u * C = (t * D) ^ 2 * (t ^ 2 * u + 2 * C) := by
  linear_combination (M * C) * h1 + (t ^ 4 * u) * h2 + (t ^ 2 * C) * h3

theorem velu2_tangent_addX_cleared_identity
    {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (W.a₁ ^ 2 * (x - x₀)
            + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (((x - x₀) ^ 2 - veluGx W x₀ y₀)
                * (6 * x ^ 2 + (4 * W.a₂ + W.a₁ ^ 2) * x + 2 * W.a₄ + W.a₁ * W.a₃)
              + veluGx W x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (x - x₀)
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
      = ((2 * y + W.a₁ * x + W.a₃) * ((x - x₀) ^ 2 - veluGx W x₀ y₀)) ^ 2
        * ((2 * y + W.a₁ * x + W.a₃) ^ 2 * (x - x₀)
            + 2
              * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
                  + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
                    * (2 * y + W.a₁ * x + W.a₃)
                  - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP hQ
  refine velu2TangentAddX_assemble ?_ ?_ ?_
  ·
    linear_combination (-4) * hP + 4 * hQ
      + (-2 * W.a₁ * x + W.a₁ * x₀ - W.a₃ - 2 * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x - 4 * x₀) * hP
      + (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * x₀) * hQ
      + (-W.a₁ ^ 2 * y₀ + W.a₁ * W.a₂ * x₀ + W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x₀ ^ 2
          - W.a₂ * W.a₃ - 2 * W.a₂ * y₀ - 2 * W.a₃ * x - W.a₃ * x₀ - 4 * x * y₀
          - 2 * x₀ * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-4 * x + 4 * x₀) * hP + (4 * x - 4 * x₀) * hQ
      + (W.a₁ ^ 2 * y₀ - 2 * W.a₁ * W.a₂ * x₀ - W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x * x₀
          - 3 * W.a₁ * x₀ ^ 2 - W.a₃ * x + W.a₃ * x₀ - 2 * x * y₀ + 2 * x₀ * y₀) * hord

end Dubon2026.SourceEllipticVelu
