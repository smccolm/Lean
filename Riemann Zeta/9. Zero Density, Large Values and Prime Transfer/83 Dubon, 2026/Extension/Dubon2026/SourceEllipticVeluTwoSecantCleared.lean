import Dubon2026.SourceEllipticVeluTwoLineRelations

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
theorem velu2_secant_negAddY_cleared_identity
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ x₁ y₁ x₂ y₂ : F}
    (hP₁ : W.toAffine.Equation x₁ y₁)
    (hP₂ : W.toAffine.Equation x₂ y₂) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) (hx12 : x₁ ≠ x₂) :
    (x₂ - x₀)
          * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
          * (x₂ - W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
          * (y₁ - y₀)
        - (x₁ - x₀)
          * ((W.a₁ * (x₂ - x₀) + y₂ - y₀)
                * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) ^ 2
              - (W.a₁ * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀)
                    + W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀)
                * (x₂ - x₀) ^ 2)
        + veluGx W x₀ y₀
          * ((W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₀) * (y₂ - y₀)
              - (x₂ - x₀)
                * (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) - y₀))
      = 0 := by
  let m := W.toAffine.slope x₁ x₂ y₁ y₂
  let b := y₁ - y₀ - m * (x₁ - x₀)
  let z := W.toAffine.addX x₁ x₂ m
  have hl₁ : y₁ - y₀ = m * (x₁ - x₀) + b := by dsimp [b]; ring
  have hl₂ : y₂ - y₀ = m * (x₂ - x₀) + b := by
    dsimp [b, m]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx12]
    have hd := sub_ne_zero.mpr hx12
    field_simp
    ring
  have hl₃ : W.toAffine.negAddY x₁ x₂ y₁ m - y₀ = m * (z - x₀) + b := by
    dsimp [z, b]
    ring
  have hs : z - x₀ = m ^ 2 + W.a₁ * m - (3 * x₀ + W.a₂) - (x₁ - x₀) - (x₂ - x₀) := by
    dsimp [z]
    ring
  have hp₁ := shifted_equation_at_two_torsion hP₁ hQ hord
  have hp₂ := shifted_equation_at_two_torsion hP₂ hQ hord
  rw [hl₁] at hp₁
  rw [hl₂] at hp₂
  have hx : x₁ - x₀ ≠ x₂ - x₀ := by
    intro h
    apply hx12
    linear_combination h
  obtain ⟨hB, hprod⟩ := secant_pair_product hx hs hp₁ hp₂
  have hid := line_y_identity hB hprod
  rw [← hl₁, ← hl₂, ← hl₃] at hid
  convert hid using 1
  dsimp only [z, m]
  ring

end Dubon2026.SourceEllipticVelu
