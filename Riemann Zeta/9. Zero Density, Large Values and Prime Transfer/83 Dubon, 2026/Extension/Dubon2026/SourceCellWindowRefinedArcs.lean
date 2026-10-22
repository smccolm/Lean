import Dubon2026.SourceCellWindowRefinement

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData.Win
noncomputable section
open scoped Real
open Set

variable {D : WinData} (W : Win D)

theorem arc_cases (k : Fin W.R.N) :
    (∃ j : ℤ, D.jlo ≤ j ∧ j ≤ D.jhi ∧
      W.R.arcSet k =
        {z : ℂ | z.im = D.Y₀ ∧ z.re ∈ Set.Icc (D.o + j * D.hm) (D.o + (j + 1) * D.hm)} ∧
      W.R.loop (W.R.φs k.castSucc) = ⟨D.o + j * D.hm, D.Y₀⟩ ∧
      W.R.loop (W.R.φs k.succ) = ⟨D.o + (j + 1) * D.hm, D.Y₀⟩ ∧
      (∀ t ∈ W.R.arcIcc k, W.R.r t = (-Real.sin t / -D.Y₀)⁻¹) ∧
      W.R.arcIcc k ⊆ Set.Ioo π (2 * π)) ∨
    (∃ j : ℤ, D.jlo ≤ j ∧ j ≤ D.jhi ∧
      W.R.arcSet k =
        {z : ℂ | z.im = D.Y₁ ∧ z.re ∈ Set.Icc (D.o + j * D.hm) (D.o + (j + 1) * D.hm)} ∧
      W.R.loop (W.R.φs k.castSucc) = ⟨D.o + (j + 1) * D.hm, D.Y₁⟩ ∧
      W.R.loop (W.R.φs k.succ) = ⟨D.o + j * D.hm, D.Y₁⟩ ∧
      (∀ t ∈ W.R.arcIcc k, W.R.r t = (Real.sin t / D.Y₁)⁻¹) ∧
      W.R.arcIcc k ⊆ Set.Ioo 0 π) ∨
    (∃ k₀ : ℤ, D.klo ≤ k₀ ∧ k₀ ≤ D.khi ∧
      W.R.arcSet k =
        {z : ℂ | z.re = D.X₀ ∧ z.im ∈ Set.Icc (D.cy (D.jlo, k₀)) (D.o + (k₀ + 1) * D.hm)} ∧
      W.R.loop (W.R.φs k.castSucc) = ⟨D.X₀, D.o + (k₀ + 1) * D.hm⟩ ∧
      W.R.loop (W.R.φs k.succ) = ⟨D.X₀, D.cy (D.jlo, k₀)⟩ ∧
      (∀ t ∈ W.R.arcIcc k, W.R.r t = (-Real.cos t / -D.X₀)⁻¹) ∧
      W.R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2)) ∨
    (∃ k₀ : ℤ, D.klo ≤ k₀ ∧ k₀ ≤ D.khi ∧
      W.R.arcSet k =
        {z : ℂ | z.re = D.X₀ ∧ z.im ∈ Set.Icc (D.o + k₀ * D.hm) (D.cy (D.jlo, k₀))} ∧
      W.R.loop (W.R.φs k.castSucc) = ⟨D.X₀, D.cy (D.jlo, k₀)⟩ ∧
      W.R.loop (W.R.φs k.succ) = ⟨D.X₀, D.o + k₀ * D.hm⟩ ∧
      (∀ t ∈ W.R.arcIcc k, W.R.r t = (-Real.cos t / -D.X₀)⁻¹) ∧
      W.R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2)) ∨
    (∃ k₀ : ℤ, D.klo ≤ k₀ ∧ k₀ ≤ D.khi ∧
      W.R.arcSet k =
        {z : ℂ | z.re = D.X₁ ∧ z.im ∈ Set.Icc (D.o + k₀ * D.hm) (D.cy (D.jhi, k₀))} ∧
      W.R.loop (W.R.φs k.castSucc) = ⟨D.X₁, D.o + k₀ * D.hm⟩ ∧
      W.R.loop (W.R.φs k.succ) = ⟨D.X₁, D.cy (D.jhi, k₀)⟩ ∧
      (∀ t ∈ W.R.arcIcc k, W.R.r t = (Real.cos t / D.X₁)⁻¹) ∧
      (W.R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨
        W.R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))) ∨
    (∃ k₀ : ℤ, D.klo ≤ k₀ ∧ k₀ ≤ D.khi ∧
      W.R.arcSet k =
        {z : ℂ | z.re = D.X₁ ∧ z.im ∈ Set.Icc (D.cy (D.jhi, k₀)) (D.o + (k₀ + 1) * D.hm)} ∧
      W.R.loop (W.R.φs k.castSucc) = ⟨D.X₁, D.cy (D.jhi, k₀)⟩ ∧
      W.R.loop (W.R.φs k.succ) = ⟨D.X₁, D.o + (k₀ + 1) * D.hm⟩ ∧
      (∀ t ∈ W.R.arcIcc k, W.R.r t = (Real.cos t / D.X₁)⁻¹) ∧
      (W.R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨
        W.R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))) := by
  obtain ⟨k₀, za, zb, hza, hzb, hzaP, hzbP, hne, hseg, hno, hA, hB, hstart, hsub⟩ := W.arc_data k
  rw [hza, hzb, hseg]
  have hno' : ∀ z ∈ D.perimPts, z ∈ segment ℝ zb za → z = zb ∨ z = za := by
    intro z hz hzs
    rw [segment_symm ℝ] at hzs
    exact (hno z hz hzs).symm
  rcases W.B.val_cases k₀ with h05 | h1 | h23 | h4
  ·
    obtain ⟨hxa, hxb, hdir⟩ := W.B.right_data h05 hA hB hstart
    have hrad : ∀ t ∈ W.R.arcIcc k, W.R.r t = (Real.cos t / D.X₁)⁻¹ := by
      intro t ht
      rw [W.hr]
      exact W.B.rad_right k₀ h05 t (hsub ht)
    have hrng : W.R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨
        W.R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2) := by
      rcases W.B.right_range h05 with h | h
      · exact Or.inl (Set.Subset.trans hsub h)
      · exact Or.inr (Set.Subset.trans hsub h)
    obtain ⟨m, hm1, hm2, hcase⟩ := D.vertical_finish D.jhi (fun h hh => D.right_pt_mem_perimPts hh)
      (D.isHt_right_of_mem hzaP hxa) (D.isHt_right_of_mem hzbP hxb) hne hxa hxb hdir hno
    rcases hcase with ⟨hset, hpa, hpb⟩ | ⟨hset, hpa, hpb⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm1, hm2, hset, hpa, hpb, hrad, hrng⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm1, hm2, hset, hpa, hpb, hrad, hrng⟩))))
  ·
    obtain ⟨hya, hyb, hdir⟩ := W.B.top_data h1 hA hB hstart
    have hrad : ∀ t ∈ W.R.arcIcc k, W.R.r t = (Real.sin t / D.Y₁)⁻¹ := by
      intro t ht
      rw [W.hr]
      exact W.B.rad_top k₀ h1 t (hsub ht)
    have hrng : W.R.arcIcc k ⊆ Set.Ioo 0 π := Set.Subset.trans hsub (W.B.rng1 k₀ h1)
    obtain ⟨j, hj1, hj2, hset, hpb, hpa⟩ :=
      D.horizontal_finish (fun n hn => D.top_mem_perimPts hn) hzbP hzaP hne.symm hyb hya hdir hno'
    rw [segment_symm ℝ za zb]
    exact Or.inr (Or.inl ⟨j, hj1, hj2, hset, hpa, hpb, hrad, hrng⟩)
  ·
    obtain ⟨hxa, hxb, hdir⟩ := W.B.left_data h23 hA hB hstart
    have hrad : ∀ t ∈ W.R.arcIcc k, W.R.r t = (-Real.cos t / -D.X₀)⁻¹ := by
      intro t ht
      rw [W.hr]
      exact W.B.rad_left k₀ h23 t (hsub ht)
    have hrng : W.R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2) :=
      Set.Subset.trans hsub (W.B.rng23 k₀ h23)
    obtain ⟨m, hm1, hm2, hcase⟩ := D.vertical_finish D.jlo (fun h hh => D.left_pt_mem_perimPts hh)
      (D.isHt_left_of_mem hzbP hxb) (D.isHt_left_of_mem hzaP hxa) hne.symm hxb hxa hdir hno'
    rw [segment_symm ℝ za zb]
    rcases hcase with ⟨hset, hpb, hpa⟩ | ⟨hset, hpb, hpa⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm1, hm2, hset, hpa, hpb, hrad, hrng⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm1, hm2, hset, hpa, hpb, hrad, hrng⟩))
  ·
    obtain ⟨hya, hyb, hdir⟩ := W.B.bottom_data h4 hA hB hstart
    have hrad : ∀ t ∈ W.R.arcIcc k, W.R.r t = (-Real.sin t / -D.Y₀)⁻¹ := by
      intro t ht
      rw [W.hr]
      exact W.B.rad_bottom k₀ h4 t (hsub ht)
    have hrng : W.R.arcIcc k ⊆ Set.Ioo π (2 * π) := Set.Subset.trans hsub (W.B.rng4 k₀ h4)
    obtain ⟨j, hj1, hj2, hset, hpa, hpb⟩ :=
      D.horizontal_finish (fun n hn => D.bottom_mem_perimPts hn) hzaP hzbP hne hya hyb hdir hno
    exact Or.inl ⟨j, hj1, hj2, hset, hpa, hpb, hrad, hrng⟩

theorem isPerimSeg_arcSet (k : Fin W.R.N) : D.IsPerimSeg (W.R.arcSet k) := by
  rcases W.arc_cases k with ⟨j, hj1, hj2, hset, -⟩ | ⟨j, hj1, hj2, hset, -⟩ |
      ⟨m, hm1, hm2, hset, -⟩ | ⟨m, hm1, hm2, hset, -⟩ | ⟨m, hm1, hm2, hset, -⟩ |
      ⟨m, hm1, hm2, hset, -⟩
  · exact Or.inl ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩, hset⟩
  · exact Or.inr (Or.inl ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩, hset⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hset⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hset⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hset⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hm2⟩, hset⟩))))

theorem exists_arc_eq {A : Set ℂ} (hA : D.IsPerimSeg A) : ∃ k : Fin W.R.N, W.R.arcSet k = A := by
  obtain ⟨S, hScard, hSmem⟩ := D.exists_finset_perimSegs
  have hmaps : Set.MapsTo W.R.arcSet (↑(Finset.univ : Finset (Fin W.R.N))) (↑S) := by
    intro k _
    exact Finset.mem_coe.mpr (hSmem _ (W.isPerimSeg_arcSet k))
  have hinj : Set.InjOn W.R.arcSet (↑(Finset.univ : Finset (Fin W.R.N))) := by
    intro k _ k' _ h
    exact arcSet_injective W.R h
  have hcard : S.card ≤ (Finset.univ : Finset (Fin W.R.N)).card := by
    rw [Finset.card_univ, Fintype.card_fin, W.N_eq]
    exact hScard
  have hsurj := Finset.surjOn_of_injOn_of_card_le W.R.arcSet hmaps hinj hcard
  obtain ⟨k, -, hk⟩ := hsurj (Finset.mem_coe.mpr (hSmem A hA))
  exact ⟨k, hk⟩

theorem exists_arc_bot (j : ℤ) (h1 : D.jlo ≤ j) (h2 : j ≤ D.jhi) :
    ∃ k : Fin W.R.N, W.R.arcSet k = D.botSeg j :=
  W.exists_arc_eq (Or.inl ⟨j, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩)

theorem exists_arc_top (j : ℤ) (h1 : D.jlo ≤ j) (h2 : j ≤ D.jhi) :
    ∃ k : Fin W.R.N, W.R.arcSet k = D.topSeg j :=
  W.exists_arc_eq (Or.inr (Or.inl ⟨j, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩))

theorem exists_arc_leftUp (k₀ : ℤ) (h1 : D.klo ≤ k₀) (h2 : k₀ ≤ D.khi) :
    ∃ k : Fin W.R.N, W.R.arcSet k = D.leftUpSeg k₀ :=
  W.exists_arc_eq (Or.inr (Or.inr (Or.inl ⟨k₀, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩)))

theorem exists_arc_leftLow (k₀ : ℤ) (h1 : D.klo ≤ k₀) (h2 : k₀ ≤ D.khi) :
    ∃ k : Fin W.R.N, W.R.arcSet k = D.leftLowSeg k₀ :=
  W.exists_arc_eq (Or.inr (Or.inr (Or.inr (Or.inl ⟨k₀, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩))))

theorem exists_arc_rightLow (k₀ : ℤ) (h1 : D.klo ≤ k₀) (h2 : k₀ ≤ D.khi) :
    ∃ k : Fin W.R.N, W.R.arcSet k = D.rightLowSeg k₀ :=
  W.exists_arc_eq
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k₀, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩)))))

theorem exists_arc_rightUp (k₀ : ℤ) (h1 : D.klo ≤ k₀) (h2 : k₀ ≤ D.khi) :
    ∃ k : Fin W.R.N, W.R.arcSet k = D.rightUpSeg k₀ :=
  W.exists_arc_eq
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k₀, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩)))))

theorem arcSet_inj (k k' : Fin W.R.N) (h : W.R.arcSet k = W.R.arcSet k') : k = k' :=
  arcSet_injective W.R h


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData.Win
