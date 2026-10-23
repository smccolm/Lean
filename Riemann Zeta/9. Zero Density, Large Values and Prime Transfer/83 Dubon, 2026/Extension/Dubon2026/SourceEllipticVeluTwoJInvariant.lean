import Dubon2026.SourceEllipticVeluTwoNonsingular

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> original
Frobenius/inertia -> good reduction -> reverse genus -> elliptic inertia orbits
-> cyclic-quotient interpretation of integral modular-polynomial roots.
This step factors the explicit classical prime-two polynomial into the j-values
of the three actual degree-two Velu curves. Identification of this explicit
polynomial with the existing integral minimal polynomial is a separate required
bridge. The quotient group homomorphism and its kernel remain required too.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the VeluQuotient2 cFour/j solutions,
Def_ModularCurve_ClassicalModularPolynomials, Def_ModularCurve_FibrePoly and
S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
theorem veluQuotient2_cFour {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x₀ y₀ : R) :
    (veluQuotient2 W x₀ y₀).c₄ = W.c₄ + 240 * veluGx W x₀ y₀ := by
  have hb₄ : (veluQuotient2 W x₀ y₀).b₄ = W.b₄ - 10 * veluGx W x₀ y₀ := by
    simp only [b₄, veluQuotient2_a₁, veluQuotient2_a₃, veluQuotient2_a₄]; ring
  simp only [c₄, veluQuotient2_b₂, hb₄]; ring

theorem veluQuotient2_j {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    haveI : (veluQuotient2 W x₀ y₀).IsElliptic :=
      isElliptic_veluQuotient2_of_isElliptic hQ hgy
    (veluQuotient2 W x₀ y₀).j
      = (W.c₄ + 240 * veluGx W x₀ y₀) ^ 3
        / (veluGx W x₀ y₀ * velu2QuadDisc W x₀ ^ 2) := by
  haveI hE : (veluQuotient2 W x₀ y₀).IsElliptic :=
    isElliptic_veluQuotient2_of_isElliptic hQ hgy
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', inv_mul_eq_div,
    veluQuotient2_cFour, veluQuotient2_Delta_eq hQ hgy]

end
end Dubon2026.SourceEllipticVelu
