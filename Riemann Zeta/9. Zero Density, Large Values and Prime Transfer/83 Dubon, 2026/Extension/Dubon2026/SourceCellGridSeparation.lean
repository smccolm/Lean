import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! DUB-17/18 -> raw reciprocity -> geometric cell dissection -> planar grid.
Choose a grid of any required small size avoiding every marked and branch
value on its boundaries and putting distinct selected values in distinct
squares. Native finite minima, dense real intervals and floor inequalities
supply the source grid conditions.
Adapted from SquareGrid in S_AlgebraicCurve_exists_dissectionScaleData,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
noncomputable section

theorem exists_mem_Ioo_notMem (T : Finset ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ t, t ∈ Set.Ioo 0 h ∧ t ∉ T := by
  have hinf : (Set.Ioo (0 : ℝ) h).Infinite :=
    Set.infinite_coe_iff.mp (Set.Ioo.infinite hh)
  obtain ⟨t, ht, hmem⟩ := (hinf.diff (T : Set ℝ).toFinite).nonempty
  exact ⟨t, ht, hmem⟩

theorem abs_sub_lt_of_floor_div_eq {x y h : ℝ} (hh : 0 < h)
    (hf : ⌊x / h⌋ = ⌊y / h⌋) : |x - y| < h := by
  have hx1 := Int.floor_le (x / h)
  have hx2 := Int.lt_floor_add_one (x / h)
  have hy1 := Int.floor_le (y / h)
  have hy2 := Int.lt_floor_add_one (y / h)
  rw [hf] at hx1 hx2
  have : |x / h - y / h| < 1 := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have h2 : |x - y| / h < 1 := by
    rw [← abs_of_pos hh, ← abs_div]
    simpa [sub_div] using this
  calc |x - y| = |x - y| / h * h := by field_simp
  _ < 1 * h := by
      exact mul_lt_mul_of_pos_right h2 hh
  _ = h := one_mul h

theorem exists_offset (C : Finset ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ t, t ∈ Set.Ioo 0 h ∧ ∀ c ∈ C, ∀ j : ℤ, c - t ≠ j * h := by
  obtain ⟨t, ht, hmem⟩ :=
    exists_mem_Ioo_notMem (C.image fun c => c - h * ⌊c / h⌋) hh
  refine ⟨t, ht, fun c hc j hcontra => hmem ?_⟩
  have hj : (j : ℝ) = ⌊c / h⌋ := by
    have h1 : c / h - t / h = j := by
      rw [← sub_div, hcontra, mul_div_assoc, div_self hh.ne', mul_one]
    have h2 : (j : ℝ) ≤ c / h := by
      have := ht.1
      have htpos : 0 < t / h := div_pos ht.1 hh
      linarith
    have h3 : c / h < j + 1 := by
      have : t / h < 1 := (div_lt_one hh).mpr ht.2
      linarith
    have := Int.floor_eq_iff.mpr ⟨h2, h3⟩
    exact_mod_cast this.symm
  refine Finset.mem_image.mpr ⟨c, hc, ?_⟩
  rw [← hj]
  linear_combination hcontra

theorem exists_separating_grid (Bad : Finset ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ o h : ℝ, 0 < h ∧ h < δ ∧
      (∀ b ∈ Bad, ∀ j : ℤ, b.re - o ≠ j * h ∧ b.im - o ≠ j * h) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' →
        ⌊(b.re - o) / h⌋ = ⌊(b'.re - o) / h⌋ → ⌊(b.im - o) / h⌋ = ⌊(b'.im - o) / h⌋ → False) := by
  classical

  set P := Bad.offDiag
  have hsep : ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧
      ∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' → s ≤ max |b.re - b'.re| |b.im - b'.im| := by
    rcases P.eq_empty_or_nonempty with hP | hP
    · refine ⟨δ, hδ, le_rfl, fun b hb b' hb' hne => absurd ?_ (Finset.eq_empty_iff_forall_notMem.mp hP ⟨b, b'⟩)⟩
      exact Finset.mem_offDiag.mpr ⟨hb, hb', hne⟩
    · refine ⟨min (P.inf' hP fun p => max |p.1.re - p.2.re| |p.1.im - p.2.im|) δ,
        lt_min ?_ hδ, min_le_right _ _, fun b hb b' hb' hne => ?_⟩
      · rw [Finset.lt_inf'_iff]
        rintro ⟨x, y⟩ hxy
        have hxyne : x ≠ y := (Finset.mem_offDiag.mp hxy).2.2
        have : x.re ≠ y.re ∨ x.im ≠ y.im := by
          by_contra hcon
          push Not at hcon
          exact hxyne (Complex.ext hcon.1 hcon.2)
        rcases this with hr | hi
        · exact lt_max_of_lt_left (abs_pos.mpr (sub_ne_zero.mpr hr))
        · exact lt_max_of_lt_right (abs_pos.mpr (sub_ne_zero.mpr hi))
      · have h5 := Finset.inf'_le (fun p : ℂ × ℂ => max |p.1.re - p.2.re| |p.1.im - p.2.im|)
          (show (b, b') ∈ P from Finset.mem_offDiag.mpr ⟨hb, hb', hne⟩)
        simp only [] at h5
        exact le_trans (min_le_left _ _) h5
  obtain ⟨s, hs0, hsδ, hsall⟩ := hsep

  set h : ℝ := s / 2 with hh_def
  have hh0 : 0 < h := by positivity
  have hhδ : h < δ := lt_of_lt_of_le (by linarith) hsδ

  obtain ⟨t, ht, havoid⟩ :=
    exists_offset ((Bad.image Complex.re) ∪ (Bad.image Complex.im)) hh0
  refine ⟨t, h, hh0, hhδ, ?_, ?_⟩
  · intro b hb j
    constructor
    · exact havoid _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)) j
    · exact havoid _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)) j
  · intro b hb b' hb' hne hfr hfi
    have h1 : |(b.re - t) - (b'.re - t)| < h := abs_sub_lt_of_floor_div_eq hh0 hfr
    have h2 : |(b.im - t) - (b'.im - t)| < h := abs_sub_lt_of_floor_div_eq hh0 hfi
    simp only [sub_sub_sub_cancel_right] at h1 h2
    have hmax : max |b.re - b'.re| |b.im - b'.im| < h := max_lt h1 h2
    have := hsall b hb b' hb' hne
    have : s < h := lt_of_le_of_lt this hmax
    rw [hh_def] at this
    linarith

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
