import Dubon2026.SourceCellRadialRegion
import Mathlib.Data.Finset.Sort

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

/-- The old and newly prescribed boundary angles. -/
def brk : Finset ℝ := Finset.univ.image R.φs ∪ T

theorem zero_mem_brk : (0 : ℝ) ∈ brk R T := by
  show (0 : ℝ) ∈ Finset.univ.image R.φs ∪ T
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, R.hφ0⟩))

theorem two_pi_mem_brk : (2 * Real.pi) ∈ brk R T := by
  show (2 * Real.pi) ∈ Finset.univ.image R.φs ∪ T
  exact Finset.mem_union.mpr
    (Or.inl (Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, R.hφN⟩))

theorem mem_brk_of_φs (i : Fin (R.N + 1)) : R.φs i ∈ brk R T := by
  show R.φs i ∈ Finset.univ.image R.φs ∪ T
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

theorem brk_nonneg (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    ∀ z ∈ brk R T, 0 ≤ z := by
  intro z hz
  have hz' : z ∈ Finset.univ.image R.φs ∪ T := hz
  rcases Finset.mem_union.mp hz' with h | h
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
    rw [← R.hφ0]
    exact R.hmono.monotone (Fin.zero_le k)
  · exact (hT z h).1

theorem brk_le (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    ∀ z ∈ brk R T, z ≤ 2 * Real.pi := by
  intro z hz
  have hz' : z ∈ Finset.univ.image R.φs ∪ T := hz
  rcases Finset.mem_union.mp hz' with h | h
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
    rw [← R.hφN]
    exact R.hmono.monotone (Fin.le_last k)
  · exact (hT z h).2

/-- Number of consecutive intervals in the refined boundary. -/
def N' : ℕ := (brk R T).card - 1

theorem brk_card : (brk R T).card = N' R T + 1 := by
  have h : 0 < (brk R T).card := Finset.card_pos.mpr ⟨0, zero_mem_brk R T⟩
  unfold N'
  omega

/-- Increasing enumeration of the complete boundary-angle set. -/
def emb : Fin (N' R T + 1) → ℝ := ⇑((brk R T).orderEmbOfFin (brk_card R T))

theorem emb_mem (i : Fin (N' R T + 1)) : emb R T i ∈ brk R T :=
  (brk R T).orderEmbOfFin_mem (brk_card R T) i

theorem emb_surj {z : ℝ} (hz : z ∈ brk R T) : ∃ i, emb R T i = z := by
  have hz' : z ∈ Set.range ((brk R T).orderEmbOfFin (brk_card R T)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast hz
  obtain ⟨i, hi⟩ := hz'
  exact ⟨i, hi⟩

theorem emb_strictMono : StrictMono (emb R T) :=
  ((brk R T).orderEmbOfFin (brk_card R T)).strictMono

theorem emb_zero (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) : emb R T 0 = 0 := by
  have h1 := (brk R T).orderEmbOfFin_zero (brk_card R T) (Nat.succ_pos (N' R T))
  have h2 : (brk R T).min' ⟨0, zero_mem_brk R T⟩ = 0 :=
    le_antisymm ((brk R T).min'_le 0 (zero_mem_brk R T))
      ((brk R T).le_min' _ _ (brk_nonneg R T hT))
  rw [← h2]
  exact h1

theorem emb_last (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * Real.pi) :
    emb R T (Fin.last (N' R T)) = 2 * Real.pi := by
  have h1 := (brk R T).orderEmbOfFin_last (brk_card R T) (Nat.succ_pos (N' R T))
  have h2 : (brk R T).max' ⟨0, zero_mem_brk R T⟩ = 2 * Real.pi :=
    le_antisymm ((brk R T).max'_le _ _ (brk_le R T hT))
      ((brk R T).le_max' _ (two_pi_mem_brk R T))
  rw [← h2]
  exact h1

theorem coe_brk : ((brk R T : Finset ℝ) : Set ℝ) = Set.range R.φs ∪ (T : Set ℝ) := by
  unfold brk
  simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem range_emb : Set.range (emb R T) = Set.range R.φs ∪ (T : Set ℝ) := by
  unfold emb
  rw [Finset.range_orderEmbOfFin]
  exact coe_brk R T


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRefine
