import Dubon2026.SourceCellGridArcReversal

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

theorem rev_per_to_sq : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
    (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit M p k = true →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (M.winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (M.winReg.arcIcc k₀) ∧
      ψ (M.winReg.φs k₀.castSucc) = (M.base p).φs k.castSucc ∧
      ψ (M.winReg.φs k₀.succ) = (M.base p).φs k.succ ∧
      ∀ t ∈ M.winReg.arcIcc k₀, M.winReg.loop t = (M.base p).loop (ψ t) := by
  intro p k k₀ hp heq hbit
  simp only [sqbit, decide_eq_true_eq] at hbit
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  have D := SideIdentity.arcData_of_rectClauses (hx₀ := (M.ctr_mem p).1.1) (hx₁ := (M.ctr_mem p).1.2) (hy₀ := (M.ctr_mem p).2.1) (hy₁ := (M.ctr_mem p).2.2) (hL₀ := (M.yL_mem p).1) (hL₁ := (M.yL_mem p).2) (M.base_spec p)
  have hqre : (M.base p).q.re = (M.ctr p).re := congrArg Complex.re (M.base_q p)
  have hqim : (M.base p).q.im = (M.ctr p).im := congrArg Complex.im (M.base_q p)
  have hwre : M.winReg.q.re = 0 := by simp [M.winReg_q]
  have hwim : M.winReg.q.im = 0 := by simp [M.winReg_q]
  have hX₁ : 0 < M.o + (M.jhi + 1) * M.hm := M.zero_mem_window.1.2
  have hY₁ : 0 < M.o + (M.khi + 1) * M.hm := M.zero_mem_window.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, l0, l1, l2, -, -, l5, l6, r05, r1, -, -, g0, g1, -, -, g5,
    -, -⟩ := M.base_spec p
  obtain ⟨-, -, -, -, -, hsix, -⟩ := M.winReg_spec
  rcases hsix k₀ with ⟨j, -, -, hset, -⟩ | ⟨j, -, -, hset, hcs, hsc, hr, hg⟩ |
    ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩ |
    ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩
  ·
    have h4 := (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2
    exfalso; omega
  ·
    have h1 := (SideIdentity.top_of_arcSet_eq M.hhm hsq (J := j) (K := M.khi) hpk.2 k (heq.trans hset)).2.2
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.hseg (M.o + (M.khi + 1) * M.hm) (M.o + j * M.hm) (M.o + (j + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.hseg_eq_hseg D.hx ((D.arc1 k h1).symm.trans (heq.trans hset'))
    refine SegmentReparam.exists_reparam_same_side.2.2.1 (M.base p) M.winReg k k₀ _ _ ?_ ?_ ?_ (r1 k h1) (g1 k h1) hr hg ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).2.2
    · linarith
    · linarith
    · rw [l1 k.castSucc (by simp [h1]), hcs]
      exact Complex.ext e₃ e₁
    · rw [l2 k.succ (by simp [h1]), hsc]
      exact Complex.ext e₂ e₁
  ·
    have h2 :=
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    exfalso; omega
  ·
    have h3 :=
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    exfalso; omega
  ·
    have h5 :=
      (SideIdentity.rightLower_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + (M.jhi + 1) * M.hm) (M.o + k₁ * M.hm) (M.cy (M.jhi, k₁)) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hc₀ ((D.arc5 k h5).symm.trans (heq.trans hset'))
    refine SegmentReparam.exists_reparam_same_side.1 (M.base p) M.winReg k k₀ _ _ ?_ ?_ ?_ (r05 k (Or.inr h5))
      (range_of_rightLower (g5 k h5)) hr hg ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · linarith
    · linarith
    · rw [l5 k.castSucc (by simp [h5]), hcs]
      exact Complex.ext e₁ e₂
    · rw [l6 k.succ (by simp [h5]), hsc]
      exact Complex.ext e₁ e₃
  ·
    have h0 :=
      (SideIdentity.rightUpper_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + (M.jhi + 1) * M.hm) (M.cy (M.jhi, k₁)) (M.o + (k₁ + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hc₁ ((D.arc0 k h0).symm.trans (heq.trans hset'))
    refine SegmentReparam.exists_reparam_same_side.1 (M.base p) M.winReg k k₀ _ _ ?_ ?_ ?_ (r05 k (Or.inl h0))
      (range_of_rightUpper (g0 k h0)) hr hg ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · linarith
    · linarith
    · rw [l0 k.castSucc (by simp [h0]), hcs]
      exact Complex.ext e₁ e₂
    · rw [l1 k.succ (by simp [h0]), hsc]
      exact Complex.ext e₁ e₃


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
