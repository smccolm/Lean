import Dubon2026.SourceEllipticOddChordIdentities

/-! Coordinate identities on the required odd-degree quotient
discriminant chain: actual quotient ellipticity -> odd-prime quotient maps
and products -> cyclic-subgroup root interpretation -> inertia census ->
reverse genus and good reduction -> DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
The native affine addition formulas are retained. Adapted from the selected
odd-order quotient discriminant proof, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The doubling numerator is supplied separately by the already proved actual
division-polynomial multiplication formula, omitting its duplicate certificate. -/
namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
section Translation

variable {V : WeierstrassCurve F}

theorem addX_two_torsion_sub_root (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xT yT : F}
    (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
    (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hT : V.toAffine.Equation xT yT) (h1 : xT ≠ e₁) :
    V.toAffine.addX e₁ xT (V.toAffine.slope e₁ xT 0 yT) - e₂
      = (e₁ - e₂) * (xT - e₃) / (xT - e₁) := by
  have eT := equation_b V ha1 ha3 hT
  have hd : xT - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd' : e₁ - xT ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [Affine.slope_of_X_ne (fun h => h1 h.symm)]
  simp only [Affine.addX, toAffine, ha1]
  field_simp
  linear_combination (norm := ring_nf) (xT - e₁) * eT
    + (2 * e₁ * xT ^ 2 - 3 * e₁ ^ 2 * xT + e₁ ^ 3) * hσ1
    + (e₁ * xT - xT ^ 2) * hσ2 + (xT - e₁) * hσ3

theorem addX_two_torsion_sub_self (ha1 : V.a₁ = 0) (ha3 : V.a₃ = 0) {e₁ e₂ e₃ xT yT : F}
    (hσ1 : e₁ + e₂ + e₃ = -V.a₂) (hσ2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = V.a₄)
    (hσ3 : e₁ * e₂ * e₃ = -V.a₆) (hT : V.toAffine.Equation xT yT) (h1 : xT ≠ e₁) :
    V.toAffine.addX e₁ xT (V.toAffine.slope e₁ xT 0 yT) - e₁
      = (e₁ - e₂) * (e₁ - e₃) / (xT - e₁) := by
  have eT := equation_b V ha1 ha3 hT
  have hd : xT - e₁ ≠ 0 := sub_ne_zero.mpr h1
  have hd' : e₁ - xT ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [Affine.slope_of_X_ne (fun h => h1 h.symm)]
  simp only [Affine.addX, toAffine, ha1]
  field_simp
  linear_combination (norm := ring_nf) (xT - e₁) * eT
    + (2 * e₁ * xT ^ 2 - 3 * e₁ ^ 2 * xT + e₁ ^ 3) * hσ1
    + (e₁ * xT - xT ^ 2) * hσ2 + (xT - e₁) * hσ3

end Translation

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
