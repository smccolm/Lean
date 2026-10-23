import Dubon2026.SourceEllipticVeluTwoNegation

/-! Surjectivity of the actual degree-two Velu point map over an algebraically
closed field. This supplies the quotient-surjectivity obligation needed to
transport cyclic subgroups, then interpret modular-polynomial roots and count
elliptic inertia orbits on the DUB-17 / DUB-18 good-reduction dependency chain.
The proof reuses the native quadratic root theorem and the same-coordinate
point/negative-point dichotomy, as in the already proved multiplication
surjectivity argument. No general isogeny or function-field machinery is needed. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] {W : WeierstrassCurve F}
  {x₀ y₀ : F}

theorem exists_velu2X_preimage (hG : veluGx W x₀ y₀ ≠ 0) (r : F) :
    ∃ x : F, x ≠ x₀ ∧ velu2X W x₀ y₀ x = r := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (-(r + x₀)) * X + C (r * x₀ + veluGx W x₀ y₀))
    (by rw [degree_quadratic one_ne_zero]; norm_num)
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hx
  have hxx : x ≠ x₀ := by
    intro heq
    subst x
    apply hG
    linear_combination hx
  refine ⟨x, hxx, ?_⟩
  have hd := sub_ne_zero.mpr hxx
  simp only [velu2X]
  field_simp
  linear_combination hx

theorem exists_equation_y (W : WeierstrassCurve F) (x : F) :
    ∃ y : F, W.toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)))
    (by rw [degree_quadratic one_ne_zero]; norm_num)
  refine ⟨y, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hy
  linear_combination hy

theorem veluPointMap2_surjective [DecidableEq F] [W.IsElliptic]
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
    (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) : Function.Surjective (veluPointMap2 hQ hgy hΔ) := by
  intro Q
  cases Q with
  | zero => exact ⟨.zero, rfl⟩
  | some r s hs =>
    obtain ⟨x, hxx, hX⟩ := exists_velu2X_preimage
      (veluGx_ne_zero_of_two_torsion W.isUnit_Δ.ne_zero hQ hgy) r
    obtain ⟨y, hy⟩ := exists_equation_y W x
    have hn : W.toAffine.Nonsingular x y := W.toAffine.equation_iff_nonsingular.mp hy
    have hn' := velu2_map_nonsingular hy hQ hgy hxx hΔ
    have he := veluPointMap2_some_of_ne hQ hgy hΔ hn hxx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := hn') (h₂ := hs)).mp hX with hh | hh
    · exact ⟨.some x y hn, he.trans hh⟩
    · refine ⟨-(WeierstrassCurve.Affine.Point.some x y hn), ?_⟩
      rw [veluPointMap2_neg hQ hgy hΔ, he, hh, neg_neg]

end
end Dubon2026.SourceEllipticVelu
