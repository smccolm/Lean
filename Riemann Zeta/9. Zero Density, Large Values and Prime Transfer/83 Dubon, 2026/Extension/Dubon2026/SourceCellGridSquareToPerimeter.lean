import Dubon2026.SourceCellGridPerimeterToSquare

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

theorem rev_sq_to_per : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
    (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit M p k = false →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((M.base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((M.base p).arcIcc k) ∧
      ψ ((M.base p).φs k.castSucc) = M.winReg.φs k₀.castSucc ∧
      ψ ((M.base p).φs k.succ) = M.winReg.φs k₀.succ ∧
      ∀ t ∈ (M.base p).arcIcc k, (M.base p).loop t = M.winReg.loop (ψ t) := by
  intro p k k₀ hp heq hbit
  simp only [sqbit, decide_eq_false_iff_not] at hbit
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  have D := SideIdentity.arcData_of_rectClauses (hx₀ := (M.ctr_mem p).1.1) (hx₁ := (M.ctr_mem p).1.2) (hy₀ := (M.ctr_mem p).2.1) (hy₁ := (M.ctr_mem p).2.2) (hL₀ := (M.yL_mem p).1) (hL₁ := (M.yL_mem p).2) (M.base_spec p)
  have hqre : (M.base p).q.re = (M.ctr p).re := congrArg Complex.re (M.base_q p)
  have hqim : (M.base p).q.im = (M.ctr p).im := congrArg Complex.im (M.base_q p)
  have hwre : M.winReg.q.re = 0 := by simp [M.winReg_q]
  have hwim : M.winReg.q.im = 0 := by simp [M.winReg_q]
  have hX₀ : M.o + M.jlo * M.hm < 0 := M.zero_mem_window.1.1
  have hY₀ : M.o + M.klo * M.hm < 0 := M.zero_mem_window.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, l2, l3, l4, l5, -, -, -, r23, r4, -, -, g23, g4, -,
    -, -⟩ := M.base_spec p
  obtain ⟨-, -, -, -, -, hsix, -⟩ := M.winReg_spec
  rcases hsix k₀ with ⟨j, -, -, hset, hcs, hsc, hr, hg⟩ | ⟨j, -, -, hset, -⟩ |
    ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩ | ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩ |
    ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩
  ·
    have h4 := (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.hseg (M.o + M.klo * M.hm) (M.o + j * M.hm) (M.o + (j + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.hseg_eq_hseg D.hx ((D.arc4 k h4).symm.trans (heq.trans hset'))
    refine SegmentReparam.exists_reparam_same_side.2.2.2 M.winReg (M.base p) k₀ k _ _ ?_ ?_ ?_ hr hg (r4 k h4) (g4 k h4) ?_ ?_
    · linarith
    · exact sub_pos.mpr (M.ctr_mem p).2.1
    · linarith
    · rw [hcs, l4 k.castSucc (by simp [h4])]
      exact Complex.ext e₂.symm e₁.symm
    · rw [hsc, l5 k.succ (by simp [h4])]
      exact Complex.ext e₃.symm e₁.symm
  ·
    have h1 := (SideIdentity.top_of_arcSet_eq M.hhm hsq (J := j) (K := M.khi) hpk.2 k (heq.trans hset)).2.2
    exfalso; omega
  ·
    have h2 :=
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + M.jlo * M.hm) (M.cy (M.jlo, k₁)) (M.o + (k₁ + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hL₁ ((D.arc2 k h2).symm.trans (heq.trans hset'))
    refine SegmentReparam.exists_reparam_same_side.2.1 M.winReg (M.base p) k₀ k _ _ ?_ ?_ ?_ hr hg (r23 k (Or.inl h2))
      (g23 k (Or.inl h2)) ?_ ?_
    · linarith
    · exact sub_pos.mpr (M.ctr_mem p).1.1
    · linarith
    · rw [hcs, l2 k.castSucc (by simp [h2])]
      exact Complex.ext e₁.symm e₃.symm
    · rw [hsc, l3 k.succ (by simp [h2])]
      exact Complex.ext e₁.symm e₂.symm
  ·
    have h3 :=
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + M.jlo * M.hm) (M.o + k₁ * M.hm) (M.cy (M.jlo, k₁)) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hL₀ ((D.arc3 k h3).symm.trans (heq.trans hset'))
    refine SegmentReparam.exists_reparam_same_side.2.1 M.winReg (M.base p) k₀ k _ _ ?_ ?_ ?_ hr hg (r23 k (Or.inr h3))
      (g23 k (Or.inr h3)) ?_ ?_
    · linarith
    · exact sub_pos.mpr (M.ctr_mem p).1.1
    · linarith
    · rw [hcs, l3 k.castSucc (by simp [h3])]
      exact Complex.ext e₁.symm e₃.symm
    · rw [hsc, l4 k.succ (by simp [h3])]
      exact Complex.ext e₁.symm e₂.symm
  ·
    have h5 :=
      (SideIdentity.rightLower_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    exfalso; omega
  ·
    have h0 :=
      (SideIdentity.rightUpper_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    exfalso; omega


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
