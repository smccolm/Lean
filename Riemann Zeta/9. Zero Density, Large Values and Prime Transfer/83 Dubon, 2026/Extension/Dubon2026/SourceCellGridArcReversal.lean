import Dubon2026.SourceCellGridArcOrientations

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
variable (M : GridData)

theorem rev_sq_sq : ∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
    (M.base p).arcSet k = (M.base p').arcSet k' → sqbit M p k = true →
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((M.base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((M.base p').arcIcc k') ∧
      ψ ((M.base p').φs k'.castSucc) = (M.base p).φs k.succ ∧
      ψ ((M.base p').φs k'.succ) = (M.base p).φs k.castSucc ∧
      ∀ t ∈ (M.base p').arcIcc k', (M.base p').loop t = (M.base p).loop (ψ t) := by
  intro p p' hne k k' heq hbit
  simp only [sqbit, decide_eq_true_eq] at hbit
  have D := SideIdentity.arcData_of_rectClauses (hx₀ := (M.ctr_mem p).1.1) (hx₁ := (M.ctr_mem p).1.2) (hy₀ := (M.ctr_mem p).2.1) (hy₁ := (M.ctr_mem p).2.2) (hL₀ := (M.yL_mem p).1) (hL₁ := (M.yL_mem p).2) (M.base_spec p)
  have D' := SideIdentity.arcData_of_rectClauses (hx₀ := (M.ctr_mem p').1.1) (hx₁ := (M.ctr_mem p').1.2) (hy₀ := (M.ctr_mem p').2.1) (hy₁ := (M.ctr_mem p').2.2) (hL₀ := (M.yL_mem p').1) (hL₁ := (M.yL_mem p').2) (M.base_spec p')
  have hqre : (M.base p).q.re = (M.ctr p).re := congrArg Complex.re (M.base_q p)
  have hqim : (M.base p).q.im = (M.ctr p).im := congrArg Complex.im (M.base_q p)
  have hqre' : (M.base p').q.re = (M.ctr p').re := congrArg Complex.re (M.base_q p')
  have hqim' : (M.base p').q.im = (M.ctr p').im := congrArg Complex.im (M.base_q p')
  obtain ⟨-, -, -, -, -, -, -, -, -, -, l0, l1, l2, -, -, l5, l6, r05, r1, -, -, g0, g1, -, -, g5,
    -, -⟩ := M.base_spec p
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, l2', l3', l4', l5', -, -, -, r23', r4', -, -, g23',
    g4', -, -, -⟩ := M.base_spec p'
  rcases pair_of_arcSet_eq M.hhm (isSquare_base M p) (isSquare_base M p') (fst_ne_or_snd_ne hne)
      k k' heq with ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
  ·
    obtain ⟨e₁, e₂, e₃⟩ :=
      SideIdentity.vseg_eq_vseg D.hc₁ ((D.arc0 k hk).symm.trans (heq.trans (D'.arc2 k' hk')))
    refine SegmentReparam.exists_reparam_across_edge.1 (M.base p) (M.base p') k k' _ _ ?_ ?_ ?_ (r05 k (Or.inl hk))
      (range_of_rightUpper (g0 k hk)) (r23' k' (Or.inl hk')) (g23' k' (Or.inl hk')) ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · exact sub_pos.mpr (M.ctr_mem p').1.1
    · linarith
    · rw [l0 k.castSucc (by simp [hk]), l3' k'.succ (by simp [hk'])]
      exact Complex.ext e₁ e₂
    · rw [l1 k.succ (by simp [hk]), l2' k'.castSucc (by simp [hk'])]
      exact Complex.ext e₁ e₃
  ·
    obtain ⟨e₁, e₂, e₃⟩ :=
      SideIdentity.vseg_eq_vseg D.hc₀ ((D.arc5 k hk).symm.trans (heq.trans (D'.arc3 k' hk')))
    refine SegmentReparam.exists_reparam_across_edge.1 (M.base p) (M.base p') k k' _ _ ?_ ?_ ?_ (r05 k (Or.inr hk))
      (range_of_rightLower (g5 k hk)) (r23' k' (Or.inr hk')) (g23' k' (Or.inr hk')) ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · exact sub_pos.mpr (M.ctr_mem p').1.1
    · linarith
    · rw [l5 k.castSucc (by simp [hk]), l4' k'.succ (by simp [hk'])]
      exact Complex.ext e₁ e₂
    · rw [l6 k.succ (by simp [hk]), l3' k'.castSucc (by simp [hk'])]
      exact Complex.ext e₁ e₃
  ·
    obtain ⟨e₁, e₂, e₃⟩ :=
      SideIdentity.hseg_eq_hseg D.hx ((D.arc1 k hk).symm.trans (heq.trans (D'.arc4 k' hk')))
    refine SegmentReparam.exists_reparam_across_edge.2 (M.base p) (M.base p') k k' _ _ ?_ ?_ ?_ (r1 k hk) (g1 k hk)
      (r4' k' hk') (g4' k' hk') ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).2.2
    · exact sub_pos.mpr (M.ctr_mem p').2.1
    · linarith
    · rw [l1 k.castSucc (by simp [hk]), l5' k'.succ (by simp [hk'])]
      exact Complex.ext e₃ e₁
    · rw [l2 k.succ (by simp [hk]), l4' k'.castSucc (by simp [hk'])]
      exact Complex.ext e₂ e₁
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
