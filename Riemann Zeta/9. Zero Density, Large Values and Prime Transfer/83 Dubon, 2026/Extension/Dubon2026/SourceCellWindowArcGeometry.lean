import Dubon2026.SourceCellWindowSegments

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow
noncomputable section
open scoped Real
open Set

variable (R : RadialRegion)

theorem φs_nonneg (i : Fin (R.N + 1)) : 0 ≤ R.φs i := by
  have h := R.hmono.monotone (Fin.zero_le i)
  rwa [R.hφ0] at h

theorem φs_le_two_pi (i : Fin (R.N + 1)) : R.φs i ≤ 2 * π := by
  have h := R.hmono.monotone (Fin.le_last i)
  rwa [R.hφN] at h

theorem φs_castSucc_lt_succ (k : Fin R.N) : R.φs k.castSucc < R.φs k.succ :=
  R.hmono Fin.castSucc_lt_succ

theorem mem_arcIcc_iff (k : Fin R.N) (t : ℝ) :
    t ∈ R.arcIcc k ↔ R.φs k.castSucc ≤ t ∧ t ≤ R.φs k.succ := by
  unfold Dubon2026.SourceFunctionField.CellGeometry.RadialRegion.arcIcc
  exact Set.mem_Icc

theorem arcIcc_subset_Icc (k : Fin R.N) : R.arcIcc k ⊆ Set.Icc 0 (2 * π) := by
  intro t ht
  rw [mem_arcIcc_iff] at ht
  exact ⟨le_trans (φs_nonneg R _) ht.1, le_trans ht.2 (φs_le_two_pi R _)⟩

theorem castSucc_mem_arcIcc (k : Fin R.N) : R.φs k.castSucc ∈ R.arcIcc k := by
  rw [mem_arcIcc_iff]
  exact ⟨le_refl _, (φs_castSucc_lt_succ R k).le⟩

theorem succ_mem_arcIcc (k : Fin R.N) : R.φs k.succ ∈ R.arcIcc k := by
  rw [mem_arcIcc_iff]
  exact ⟨(φs_castSucc_lt_succ R k).le, le_refl _⟩

theorem mem_arcSet_iff (k : Fin R.N) (z : ℂ) :
    z ∈ R.arcSet k ↔ ∃ t ∈ R.arcIcc k, R.loop t = z := by
  unfold Dubon2026.SourceFunctionField.CellGeometry.RadialRegion.arcSet
  exact Set.mem_image _ _ _

theorem loop_mem_arcSet (k : Fin R.N) {t : ℝ} (ht : t ∈ R.arcIcc k) : R.loop t ∈ R.arcSet k :=
  (mem_arcSet_iff R k _).mpr ⟨t, ht, rfl⟩

theorem loop_two_pi : R.loop (2 * Real.pi) = R.loop 0 := by
  simpa only [zero_add] using R.loop_periodic 0

theorem loop_injOn_Ico : Set.InjOn R.loop (Set.Ico 0 (2 * Real.pi)) :=
  PowPullback.injOn_loop_of_radialRegion R

theorem eq_of_loop_eq {s t : ℝ} (hs : s ∈ Set.Icc 0 (2 * π)) (ht : t ∈ Set.Icc 0 (2 * π))
    (h : R.loop s = R.loop t) : s = t ∨ (s = 0 ∧ t = 2 * π) ∨ (s = 2 * π ∧ t = 0) := by
  have hπ := Real.pi_pos
  have h0m : (0 : ℝ) ∈ Set.Ico 0 (2 * π) := ⟨le_refl _, by linarith⟩
  obtain ⟨hs0, hs2'⟩ := hs
  obtain ⟨ht0, ht2'⟩ := ht
  rcases eq_or_lt_of_le hs2' with hs2 | hs2 <;> rcases eq_or_lt_of_le ht2' with ht2 | ht2
  · exact Or.inl (hs2.trans ht2.symm)
  ·
    rw [hs2, loop_two_pi R] at h
    have htm : t ∈ Set.Ico 0 (2 * π) := ⟨ht0, ht2⟩
    have h0 : (0 : ℝ) = t := loop_injOn_Ico R h0m htm h
    exact Or.inr (Or.inr ⟨hs2, h0.symm⟩)
  · rw [ht2, loop_two_pi R] at h
    have hsm : s ∈ Set.Ico 0 (2 * π) := ⟨hs0, hs2⟩
    have h0 : s = 0 := loop_injOn_Ico R hsm h0m h
    exact Or.inr (Or.inl ⟨h0, ht2⟩)
  · have hsm : s ∈ Set.Ico 0 (2 * π) := ⟨hs0, hs2⟩
    have htm : t ∈ Set.Ico 0 (2 * π) := ⟨ht0, ht2⟩
    exact Or.inl (loop_injOn_Ico R hsm htm h)

theorem arcSet_injective {k k' : Fin R.N} (h : R.arcSet k = R.arcSet k') : k = k' := by
  have hπ := Real.pi_pos
  by_contra hne
  have hab := φs_castSucc_lt_succ R k
  have ha0 := φs_nonneg R k.castSucc
  have hb2 := φs_le_two_pi R k.succ
  have hm : (R.φs k.castSucc + R.φs k.succ) / 2 ∈ R.arcIcc k := by
    rw [mem_arcIcc_iff]
    exact ⟨by linarith, by linarith⟩
  have hmem : R.loop ((R.φs k.castSucc + R.φs k.succ) / 2) ∈ R.arcSet k' := by
    rw [← h]
    exact loop_mem_arcSet R k hm
  rw [mem_arcSet_iff] at hmem
  obtain ⟨t, ht, hteq⟩ := hmem
  have ht' := arcIcc_subset_Icc R k' ht

  have hmid : (R.φs k.castSucc + R.φs k.succ) / 2 ∈ Set.Icc 0 (2 * π) := ⟨by linarith, by linarith⟩
  have htm : t = (R.φs k.castSucc + R.φs k.succ) / 2 := by
    rcases eq_of_loop_eq R ht' hmid hteq with h1 | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact h1
    · exfalso
      linarith
    · exfalso
      linarith
  rw [htm, mem_arcIcc_iff] at ht
  rcases lt_or_gt_of_ne hne with hlt | hlt
  ·
    have hle : k.succ ≤ k'.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      rw [Fin.lt_def] at hlt
      omega
    have h1 : R.φs k.succ ≤ R.φs k'.castSucc := R.hmono.monotone hle
    linarith [ht.1]
  · have hlt' : k' < k := hlt
    have hle : k'.succ ≤ k.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      rw [Fin.lt_def] at hlt'
      omega
    have h1 : R.φs k'.succ ≤ R.φs k.castSucc := R.hmono.monotone hle
    linarith [ht.2]

theorem loop_castSucc_ne_loop_succ (hN : 2 ≤ R.N) (k : Fin R.N) :
    R.loop (R.φs k.castSucc) ≠ R.loop (R.φs k.succ) := by
  intro h
  have hab := φs_castSucc_lt_succ R k
  have ha := φs_nonneg R k.castSucc
  have hb := φs_le_two_pi R k.succ
  have ham : R.φs k.castSucc ∈ Set.Icc 0 (2 * π) := ⟨ha, by linarith⟩
  have hbm : R.φs k.succ ∈ Set.Icc 0 (2 * π) := ⟨by linarith, hb⟩
  rcases eq_of_loop_eq R ham hbm h with h1 | ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact absurd h1 hab.ne
  ·
    have hk0 : k.castSucc = 0 := R.hmono.injective (by rw [h1, R.hφ0])
    have hkN : k.succ = Fin.last R.N := R.hmono.injective (by rw [h2, R.hφN])
    have e0 : (k : ℕ) = 0 := by
      have e := congrArg Fin.val hk0
      simpa using e
    have eN : (k : ℕ) + 1 = R.N := by
      have e := congrArg Fin.val hkN
      simpa using e
    omega
  · linarith


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow
