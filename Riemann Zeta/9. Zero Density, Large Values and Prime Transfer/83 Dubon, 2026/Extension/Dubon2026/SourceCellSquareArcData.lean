import Dubon2026.SourceCellSideSegments

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
noncomputable section
open scoped Real
open Set

/-- The six exact side images and their strict endpoint bounds. -/
structure ArcData (R : RadialRegion) (x₀ x₁ y₀ y₁ yc yL : ℝ) : Prop where
  hx : x₀ < x₁
  hc₀ : y₀ < yc
  hc₁ : yc < y₁
  hL₀ : y₀ < yL
  hL₁ : yL < y₁
  hN : R.N = 6
  arc0 : ∀ a : Fin R.N, a.val = 0 → R.arcSet a = vseg x₁ yc y₁
  arc1 : ∀ a : Fin R.N, a.val = 1 → R.arcSet a = hseg y₁ x₀ x₁
  arc2 : ∀ a : Fin R.N, a.val = 2 → R.arcSet a = vseg x₀ yL y₁
  arc3 : ∀ a : Fin R.N, a.val = 3 → R.arcSet a = vseg x₀ y₀ yL
  arc4 : ∀ a : Fin R.N, a.val = 4 → R.arcSet a = hseg y₀ x₀ x₁
  arc5 : ∀ a : Fin R.N, a.val = 5 → R.arcSet a = vseg x₁ y₀ yc

theorem arcData_of_rectClauses {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ} {hx₀ : x₀ < p.re} {hx₁ : p.re < x₁}
    {hy₀ : y₀ < p.im} {hy₁ : p.im < y₁} {hL₀ : y₀ < yL} {hL₁ : yL < y₁} {R : RadialRegion}
    (h : PlanarRegions.RectClauses x₀ x₁ y₀ y₁ p yL R) : ArcData R x₀ x₁ y₀ y₁ p.im yL := by
  obtain ⟨-, hN, -, -, h0, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨hx₀.trans hx₁, hy₀, hy₁, hL₀, hL₁, hN, h0, h1, h2, h3, h4, h5⟩

theorem arcData_of_isSquare {o hm : ℝ} {j k : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm j k c yL R) :
    ArcData R (o + j * hm) (o + (j + 1) * hm) (o + k * hm) (o + (k + 1) * hm) c.im yL := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁, hL₀, hL₁, hc⟩ := h
  exact arcData_of_rectClauses (hx₀ := hx₀) (hx₁ := hx₁) (hy₀ := hy₀) (hy₁ := hy₁) (hL₀ := hL₀) (hL₁ := hL₁) hc


theorem ArcData.arcSet_cases {R : RadialRegion} {x₀ x₁ y₀ y₁ yc yL : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (a : Fin R.N) :
    (a.val = 0 ∧ R.arcSet a = vseg x₁ yc y₁) ∨ (a.val = 1 ∧ R.arcSet a = hseg y₁ x₀ x₁) ∨
    (a.val = 2 ∧ R.arcSet a = vseg x₀ yL y₁) ∨ (a.val = 3 ∧ R.arcSet a = vseg x₀ y₀ yL) ∨
    (a.val = 4 ∧ R.arcSet a = hseg y₀ x₀ x₁) ∨ (a.val = 5 ∧ R.arcSet a = vseg x₁ y₀ yc) := by
  have hN := D.hN
  have hlt := a.isLt
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 ∨ a.val = 5) with
    h | h | h | h | h | h
  · exact Or.inl ⟨h, D.arc0 a h⟩
  · exact Or.inr (Or.inl ⟨h, D.arc1 a h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, D.arc2 a h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, D.arc3 a h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, D.arc4 a h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, D.arc5 a h⟩))))

theorem ArcData.arcSet_injective {R : RadialRegion} {x₀ x₁ y₀ y₁ yc yL : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) : ∀ a a' : Fin R.N, R.arcSet a = R.arcSet a' → a = a' := by
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hy := D.hc₀.trans D.hc₁
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | exact Fin.ext (by omega)
    | exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg (by assumption))
    | refine (vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))
    | exact absurd _e₂ (ne_of_gt (by assumption))


end
end Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
