import Dubon2026.SourceEllipticVeluTwoDiscriminants

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

theorem veluGx_ne_zero_of_two_torsion (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    veluGx W x₀ y₀ ≠ 0 := by
  intro h
  apply hΔ
  rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h]
  simp

theorem velu2QuadDisc_ne_zero_of_two_torsion (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    velu2QuadDisc W x₀ ≠ 0 := by
  intro h
  apply hΔ
  rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h, mul_zero]

theorem veluQuotient2_Delta_ne_zero [NoZeroDivisors R] (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    (veluQuotient2 W x₀ y₀).Δ ≠ 0 := by
  rw [veluQuotient2_Delta_eq hQ hgy]
  exact mul_ne_zero (veluGx_ne_zero_of_two_torsion hΔ hQ hgy)
    (pow_ne_zero 2 (velu2QuadDisc_ne_zero_of_two_torsion hΔ hQ hgy))

theorem isElliptic_veluQuotient2_of_isElliptic
    {F : Type*} [Field F] {E : WeierstrassCurve F} [E.IsElliptic] {x y : F}
    (hQ : E.toAffine.Equation x y) (hgy : veluGy E x y = 0) :
    (veluQuotient2 E x y).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (veluQuotient2_Delta_ne_zero E.isUnit_Δ.ne_zero hQ hgy)⟩

end
end Dubon2026.SourceEllipticVelu
