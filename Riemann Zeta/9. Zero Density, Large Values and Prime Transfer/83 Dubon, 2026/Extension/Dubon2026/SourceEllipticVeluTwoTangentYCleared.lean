import Dubon2026.SourceEllipticVeluTwoTangentXCleared

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
theorem velu2_tangent_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hy : y ≠ W.toAffine.negY x y) :
    (x - x₀) * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
          * (x - W.toAffine.addX x x (W.toAffine.slope x x y y)) * (y - y₀)
        - (x - x₀)
          * ((W.a₁ * (x - x₀) + y - y₀)
                * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀)
                    + W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀)
                * (x - x₀) ^ 2)
        + veluGx W x₀ y₀
          * ((W.toAffine.addX x x (W.toAffine.slope x x y y) - x₀) * (y - y₀)
              - (x - x₀) * (W.toAffine.negAddY x x y (W.toAffine.slope x x y y) - y₀))
      = 0 := by
  let m := W.toAffine.slope x x y y
  let b := y - y₀ - m * (x - x₀)
  let z := W.toAffine.addX x x m
  have hl : y - y₀ = m * (x - x₀) + b := by dsimp [b]; ring
  have hl₃ : W.toAffine.negAddY x x y m - y₀ = m * (z - x₀) + b := by
    dsimp [z, b]
    ring
  have hs : z - x₀ = m ^ 2 + W.a₁ * m - (3 * x₀ + W.a₂) - 2 * (x - x₀) := by
    dsimp [z]
    ring
  have hp := shifted_equation_at_two_torsion hP hQ hord
  rw [hl] at hp
  have hm : m * (y - W.toAffine.negY x y) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    dsimp [m]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hy)
  have hD : m * (2 * (m * (x - x₀) + b) + W.a₁ * (x - x₀)) =
      3 * (x - x₀) ^ 2 + 2 * (3 * x₀ + W.a₂) * (x - x₀) +
        veluGx W x₀ y₀ - W.a₁ * (m * (x - x₀) + b) := by
    rw [← hl]
    simp only [veluGx]
    simp only [WeierstrassCurve.Affine.negY] at hm
    linear_combination hm - m * hord
  obtain ⟨hB, hprod⟩ := tangent_pair_product hs hp hD
  have hid := line_y_identity hB hprod
  rw [← hl, ← hl₃] at hid
  convert hid using 1
  dsimp only [z, m]
  ring

end Dubon2026.SourceEllipticVelu
