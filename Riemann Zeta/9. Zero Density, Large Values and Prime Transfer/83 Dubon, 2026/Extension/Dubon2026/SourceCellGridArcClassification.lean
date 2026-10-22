import Dubon2026.SourceCellSideRealization
import Dubon2026.SourceCellEdgeReparametrizations

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
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
noncomputable section
open scoped Real
open Set

open PlanarRegions

theorem arcData_right_pair {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : SideIdentity.ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : SideIdentity.ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₀ : y₀' = y₀) (hy₁ : y₁' = y₁) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  subst hx hy₀ hy₁
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hx' := D'.hx
  have _hc₀' := D'.hc₀
  have _hc₁' := D'.hc₁
  have _hL₀' := D'.hL₀
  have _hL₁' := D'.hL₁
  have _hy := D.hc₀.trans D.hc₁
  have _hxx := D.hx.trans D'.hx
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D'.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | omega
    | exact absurd (ea.symm.trans (heq.trans ea')) (SideIdentity.vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (SideIdentity.hseg_ne_vseg (by assumption))
    | refine (SideIdentity.vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (SideIdentity.hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))
    | exact absurd _e₂ (ne_of_gt (by assumption))

theorem right_of_arcSet_eq' {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : SideIdentity.IsSquare o hm j k c yL R) (h' : SideIdentity.IsSquare o hm (j+1) k c' yL' R') :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  have D := SideIdentity.arcData_of_isSquare h
  have D' := SideIdentity.arcData_of_isSquare h'
  exact arcData_right_pair D D' (by simp) rfl rfl

theorem fst_ne_or_snd_ne {p p' : ℤ × ℤ} (h : p ≠ p') : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
  rcases ne_or_eq p.1 p'.1 with h₁ | h₁
  · exact Or.inl h₁
  · exact Or.inr fun h₂ => h (Prod.ext h₁ h₂)

theorem pair_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k j' k' : ℤ} {c c' : ℂ} {yL yL' : ℝ}
    {R R' : RadialRegion} (h : SideIdentity.IsSquare o hm j k c yL R) (h' : SideIdentity.IsSquare o hm j' k' c' yL' R')
    (hne : j ≠ j' ∨ k ≠ k') (a : Fin R.N) (a' : Fin R'.N) (heq : R.arcSet a = R'.arcSet a') :
    (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) ∨ (a.val = 1 ∧ a'.val = 4) ∨
      (a.val = 2 ∧ a'.val = 0) ∨ (a.val = 3 ∧ a'.val = 5) ∨ (a.val = 4 ∧ a'.val = 1) := by
  rcases SideIdentity.locality hhm h h' a a' heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne.elim (fun hj => (hj rfl).elim) (fun hk => (hk rfl).elim)
  · rcases right_of_arcSet_eq' h h' a a' heq with h₀₂ | h₅₃
    · exact Or.inl h₀₂
    · exact Or.inr (Or.inl h₅₃)
  · rcases right_of_arcSet_eq' h' h a' a heq.symm with ⟨h₀, h₂⟩ | ⟨h₅, h₃⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₂, h₀⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₃, h₅⟩))))
  · exact Or.inr (Or.inr (Or.inl (SideIdentity.upper_of_arcSet_eq h h' a a' heq)))
  · obtain ⟨h₁, h₄⟩ := SideIdentity.upper_of_arcSet_eq h' h a' a heq.symm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h₄, h₁⟩))))

theorem range_of_rightUpper {A : Set ℝ} (h : A ⊆ Ico 0 (π / 2)) :
    A ⊆ Ioo (-(π / 2)) (π / 2) ∨ A ⊆ Ioo (3 * π / 2) (5 * π / 2) :=
  Or.inl fun t ht => ⟨by linarith [(h ht).1, Real.pi_pos], (h ht).2⟩

theorem range_of_rightLower {A : Set ℝ} (h : A ⊆ Ioc (3 * π / 2) (2 * π)) :
    A ⊆ Ioo (-(π / 2)) (π / 2) ∨ A ⊆ Ioo (3 * π / 2) (5 * π / 2) :=
  Or.inr fun t ht => ⟨(h ht).1, by linarith [(h ht).2, Real.pi_pos]⟩

variable (M : GridData)

theorem isSquare_base (p : ℤ × ℤ) : SideIdentity.IsSquare M.o M.hm p.1 p.2 (M.ctr p) (M.yL p) (M.base p) := by
  unfold SideIdentity.IsSquare
  exact ⟨(M.ctr_mem p).1.1, (M.ctr_mem p).1.2, (M.ctr_mem p).2.1, (M.ctr_mem p).2.2,
    (M.yL_mem p).1, (M.yL_mem p).2, M.base_spec p⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
