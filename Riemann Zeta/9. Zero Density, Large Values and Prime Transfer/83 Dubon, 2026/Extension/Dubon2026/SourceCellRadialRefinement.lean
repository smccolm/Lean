import Dubon2026.SourceCellRefinementBreaks

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRefine
noncomputable section
open scoped Real
open Set

variable (R : RadialRegion) (T : Finset ℝ)

theorem harc (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) (k' : Fin (N' R T)) :
    ∃ k : Fin R.N,
      R.φs k.castSucc ≤ emb R T k'.castSucc ∧ emb R T k'.succ ≤ R.φs k.succ := by
  classical
  have hab : emb R T k'.castSucc < emb R T k'.succ := emb_strictMono R T Fin.castSucc_lt_succ
  set a := emb R T k'.castSucc with ha
  set b := emb R T k'.succ with hb
  have haS := emb_mem R T k'.castSucc
  have hbS := emb_mem R T k'.succ
  set lows : Finset (Fin (R.N + 1)) := Finset.univ.filter (fun k => R.φs k ≤ a)
    with hlows
  have hlne : lows.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [R.hφ0]
    exact brk_nonneg R T hT _ haS
  set k₀ : Fin (R.N + 1) := lows.max' hlne with hk₀def
  have hk₀ : R.φs k₀ ≤ a := (Finset.mem_filter.mp (lows.max'_mem hlne)).2
  have hk₀max : ∀ j : Fin (R.N + 1), R.φs j ≤ a → j ≤ k₀ := fun j hj =>
    lows.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  have hk₀lt : k₀ < Fin.last R.N := by
    rcases lt_or_eq_of_le (Fin.le_last k₀) with h | h
    · exact h
    · exfalso
      rw [h, R.hφN] at hk₀
      have hble := brk_le R T hT _ hbS
      linarith
  set k : Fin R.N := k₀.castPred hk₀lt.ne with hkdef
  have hkc : k.castSucc = k₀ := Fin.castSucc_castPred _ _
  refine ⟨k, by rw [hkc]; exact hk₀, ?_⟩
  have hlt : a < R.φs k.succ := by
    by_contra hcon
    push Not at hcon
    have h1 := hk₀max k.succ hcon
    rw [← hkc] at h1
    exact absurd Fin.castSucc_lt_succ (not_lt.mpr h1)
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := emb_surj R T (mem_brk_of_φs R T k.succ)
  have hj1 : k'.castSucc < j := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hlt
  have hj2 : j < k'.succ := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hcon
  rw [Fin.lt_def] at hj1 hj2
  rw [Fin.val_castSucc] at hj1
  rw [Fin.val_succ] at hj2
  omega

theorem emb_consec (k' : Fin (N' R T)) :
    ∀ t ∈ brk R T, t ∉ Set.Ioo (emb R T k'.castSucc) (emb R T k'.succ) := by
  intro t ht hmem
  obtain ⟨j, hj⟩ := emb_surj R T ht
  have hj1 : k'.castSucc < j := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hmem.1
  have hj2 : j < k'.succ := by
    refine (emb_strictMono R T).lt_iff_lt.mp ?_
    rw [hj]
    exact hmem.2
  rw [Fin.lt_def] at hj1 hj2
  rw [Fin.val_castSucc] at hj1
  rw [Fin.val_succ] at hj2
  omega

/-- The same radial region with exactly the prescribed refined angles. -/
noncomputable def refineExact (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) : RadialRegion where
  q := R.q
  r := R.r
  hcont := R.hcont
  hper := R.hper
  hpos := R.hpos
  N := N' R T
  φs := emb R T
  hφ0 := emb_zero R T hT
  hφN := emb_last R T hT
  hmono := emb_strictMono R T
  hC2 := fun k' => by
    obtain ⟨k, h1, h2⟩ := harc R T hT k'
    exact (R.hC2 k).mono (Set.Icc_subset_Icc h1 h2)

theorem refineExact_q (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).q = R.q := rfl

theorem refineExact_r (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).r = R.r := rfl

theorem refineExact_K (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).K = R.K := rfl

theorem refineExact_Kint (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).Kint = R.Kint := rfl

theorem refineExact_loop (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).loop = R.loop := rfl

theorem range_φs (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    Set.range (refineExact R T hT).φs = Set.range R.φs ∪ (T : Set ℝ) :=
  range_emb R T

theorem N_add_one_ncard (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    (refineExact R T hT).N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard := by
  rw [← coe_brk R T, Set.ncard_coe_finset]
  exact (brk_card R T).symm

theorem not_mem_Ioo_φs (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) (k : Fin (refineExact R T hT).N) :
    ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
      t ∉ Set.Ioo ((refineExact R T hT).φs k.castSucc) ((refineExact R T hT).φs k.succ) := by
  intro t ht
  rw [← coe_brk R T] at ht
  exact emb_consec R T k t (Finset.mem_coe.mp ht)

theorem exists_arcIcc_subset (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi)
    (k' : Fin (refineExact R T hT).N) :
    ∃ k : Fin R.N, (refineExact R T hT).arcIcc k' ⊆ R.arcIcc k := by
  obtain ⟨k, h1, h2⟩ := harc R T hT k'
  exact ⟨k, Set.Icc_subset_Icc h1 h2⟩



open scoped Real
open Set

theorem exists_refine_exact (R : RadialRegion) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * π) :
    ∃ R' : RadialRegion,
      R'.q = R.q ∧ R'.r = R.r ∧ R'.K = R.K ∧ R'.Kint = R.Kint ∧ R'.loop = R.loop ∧
      Set.range R'.φs = Set.range R.φs ∪ (T : Set ℝ) ∧
      R'.N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard ∧
      (∀ k' : Fin R'.N, ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
        t ∉ Ioo (R'.φs k'.castSucc) (R'.φs k'.succ)) ∧
      (∀ k' : Fin R'.N, ∃ k : Fin R.N, R'.arcIcc k' ⊆ R.arcIcc k) := by
  exact ⟨refineExact R T hT, refineExact_q R T hT, refineExact_r R T hT, refineExact_K R T hT,
    refineExact_Kint R T hT, refineExact_loop R T hT, range_φs R T hT, N_add_one_ncard R T hT,
    not_mem_Ioo_φs R T hT, exists_arcIcc_subset R T hT⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRefine
