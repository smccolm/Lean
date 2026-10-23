import Dubon2026.SourceEllipticVeluTwoEquation

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
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
variable {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
  (hgy : veluGy W x₀ y₀ = 0) (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)

open scoped Classical in

/-- The actual degree-two quotient map on nonsingular points. -/
def veluPointMap2 :
    W.toAffine.Point → (veluQuotient2 W x₀ y₀).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x = x₀ then .zero
    else .some (velu2X W x₀ y₀ x) (velu2Y W x₀ y₀ x y)
      (velu2_map_nonsingular h.1 hQ hgy hx hΔ)

@[simp] theorem veluPointMap2_zero : veluPointMap2 hQ hgy hΔ .zero = .zero := rfl

theorem veluPointMap2_some_of_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x = x₀) :
    veluPointMap2 hQ hgy hΔ (.some x y h) = .zero := by
  simp only [veluPointMap2]
  exact dif_pos hx

theorem veluPointMap2_some_of_ne {x y : F} (h : W.toAffine.Nonsingular x y) (hx : x ≠ x₀) :
    veluPointMap2 hQ hgy hΔ (.some x y h)
      = .some _ _ (velu2_map_nonsingular h.1 hQ hgy hx hΔ) := by
  simp only [veluPointMap2]
  exact dif_neg hx


end
end Dubon2026.SourceEllipticVelu
