import Dubon2026.SourceEllipticVeluTwoRationalCoordinates

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> original
Frobenius/inertia -> good reduction -> reverse genus -> elliptic inertia orbits
-> actual cyclic-quotient interpretation of integral modular-polynomial roots
-> the degree-two quotient group map and its kernel.
This step constructs the actual rational coordinate map on nonsingular points
and identifies its zero fiber. Additivity remains a separate required proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Def_WeierstrassCurve_VeluPointMap2 and
the kernel geometry in S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2.
The cleared equation is proved by eliminating two coefficients and factoring
the remaining point equation, without the source certificate's factor four. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem velu2_map_equation {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hx : x ≠ x₀) :
    (veluQuotient2 W x₀ y₀).toAffine.Equation
      (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := velu2_equation_cleared W hP hQ hgy
  rw [WeierstrassCurve.Affine.equation_iff, velu2X_eq_div W x₀ y₀ hx,
    velu2Y_eq_div W x₀ y₀ y hx]
  simp only [veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₃,
    veluQuotient2_a₄, veluQuotient2_a₆]
  field_simp
  linear_combination key

variable {W} in
theorem velu2_map_nonsingular {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hx : x ≠ x₀)
    (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) :
    (veluQuotient2 W x₀ y₀).toAffine.Nonsingular
      (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y) :=
  ((veluQuotient2 W x₀ y₀).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    (velu2_map_equation W hP hQ hgy hx)

end
end Dubon2026.SourceEllipticVelu
