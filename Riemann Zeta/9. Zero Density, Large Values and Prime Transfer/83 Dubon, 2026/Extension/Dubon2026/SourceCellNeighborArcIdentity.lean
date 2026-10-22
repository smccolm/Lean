import Dubon2026.SourceCellSquareArcData

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

theorem ArcData.right_eq₀₂ {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₁ : y₁' = y₁) (hL : yL' = yc)
    (a : Fin R.N) (ha : a.val = 0) (a' : Fin R'.N) (ha' : a'.val = 2) : R.arcSet a = R'.arcSet a' := by
  subst hx hy₁ hL
  rw [D.arc0 a ha, D'.arc2 a' ha']

theorem ArcData.right_eq₅₃ {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₀ : y₀' = y₀) (hL : yL' = yc)
    (a : Fin R.N) (ha : a.val = 5) (a' : Fin R'.N) (ha' : a'.val = 3) : R.arcSet a = R'.arcSet a' := by
  subst hx hy₀ hL
  rw [D.arc5 a ha, D'.arc3 a' ha']

theorem ArcData.right_pair {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₀ : y₀' = y₀) (hy₁ : y₁' = y₁) (hL : yL' = yc) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  subst hx hy₀ hy₁ hL
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hx' := D'.hx
  have _hc₀' := D'.hc₀
  have _hc₁' := D'.hc₁
  have _hy := D.hc₀.trans D.hc₁
  have _hxx := D.hx.trans D'.hx
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D'.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | omega
    | exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg (by assumption))
    | refine (vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))
    | exact absurd _e₂ (ne_of_gt (by assumption))

theorem ArcData.upper_eq₁₄ {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₂ yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₂ yc' yL')
    (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (hy : y₀' = y₁)
    (a : Fin R.N) (ha : a.val = 1) (a' : Fin R'.N) (ha' : a'.val = 4) : R.arcSet a = R'.arcSet a' := by
  subst hx₀ hx₁ hy
  rw [D.arc1 a ha, D'.arc4 a' ha']

theorem ArcData.upper_pair {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₂ yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₂ yc' yL')
    (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (hy : y₀' = y₁) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' → a.val = 1 ∧ a'.val = 4 := by
  subst hx₀ hx₁ hy
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hc₀' := D'.hc₀
  have _hc₁' := D'.hc₁
  have _hL₀' := D'.hL₀
  have _hL₁' := D'.hL₁
  have _hy₀₁ := D.hc₀.trans D.hc₁
  have _hy₁₂ := D'.hc₀.trans D'.hc₁
  have _hy₀₂ := _hy₀₁.trans _hy₁₂
  have _hcc := D.hc₁.trans D'.hc₀
  have _hLL := D.hL₁.trans D'.hL₀
  have _hyc' := _hy₀₁.trans D'.hc₀
  have _hyL' := _hy₀₁.trans D'.hL₀
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D'.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | omega
    | exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg (by assumption))
    | refine (vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))

theorem arcSet_injective {o hm : ℝ} {j k : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm j k c yL R) : ∀ a a' : Fin R.N, R.arcSet a = R.arcSet a' → a = a' :=
  (arcData_of_isSquare h).arcSet_injective


theorem right_arcSet_eq₀₂ {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm (j+1) k c' yL' R') (hsplit : yL' = c.im) :
    ∀ a : Fin R.N, a.val = 0 → ∀ a' : Fin R'.N, a'.val = 2 → R.arcSet a = R'.arcSet a' := by
  intro a ha a' ha'
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.right_eq₀₂ D' (by simp) rfl hsplit a ha a' ha'

theorem right_arcSet_eq₅₃ {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm (j+1) k c' yL' R') (hsplit : yL' = c.im) :
    ∀ a : Fin R.N, a.val = 5 → ∀ a' : Fin R'.N, a'.val = 3 → R.arcSet a = R'.arcSet a' := by
  intro a ha a' ha'
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.right_eq₅₃ D' (by simp) rfl hsplit a ha a' ha'

theorem right_of_arcSet_eq {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm (j+1) k c' yL' R') (hsplit : yL' = c.im) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.right_pair D' (by simp) rfl rfl hsplit

theorem upper_arcSet_eq₁₄ {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm j (k+1) c' yL' R') :
    ∀ a : Fin R.N, a.val = 1 → ∀ a' : Fin R'.N, a'.val = 4 → R.arcSet a = R'.arcSet a' := by
  intro a ha a' ha'
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.upper_eq₁₄ D' rfl rfl (by simp) a ha a' ha'

theorem upper_of_arcSet_eq {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm j (k+1) c' yL' R') :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' → a.val = 1 ∧ a'.val = 4 := by
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.upper_pair D' rfl rfl (by simp)


end
end Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
