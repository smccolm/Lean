import Dubon2026.RealVerticalJets
import Dubon2026.SublevelCover

/-! # Finite derivative patches for the compact family of prime twists -/

namespace Dubon2026

open Set MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section

/-- Data describing a phase rectangle and a selected real component of a vertical derivative. -/
structure VerticalJetPatch (N : ℕ) where
  /-- Order of the selected derivative. -/
  order : ℕ
  /-- Choice of real or imaginary component. -/
  component : Bool
  /-- Phase neighborhood. -/
  phases : Set (PrimeTorus N)
  /-- Left height endpoint. -/
  left : ℝ
  /-- Right height endpoint. -/
  right : ℝ
  /-- Proposed positive lower bound on the selected derivative. -/
  lower : ℝ

/-- The open height rectangle associated to a patch. -/
def VerticalJetPatch.region {N : ℕ} (p : VerticalJetPatch N) : Set (PrimeTorus N × ℝ) :=
  p.phases ×ˢ Ioo p.left p.right

theorem exists_vertical_jet_patch {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (zt : PrimeTorus N × ℝ) :
    ∃ p : VerticalJetPatch N, IsOpen p.phases ∧ zt ∈ p.region ∧ 0 < p.lower ∧
      ∀ w ∈ p.phases, ∀ u ∈ Icc p.left p.right,
        p.lower ≤ |realVerticalJet a N σ p.order p.component w u| := by
  obtain ⟨k, b, U, l, r, L, hU, hz, hl, hr, hL, hb⟩ :=
    exists_vertical_jet_rectangle hN ha σ zt.1 zt.2
  exact ⟨⟨k, b, U, l, r, L⟩, hU, ⟨hz, hl, hr⟩, hL, hb⟩

theorem exists_finite_vertical_jet_cover {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    ∃ s : Finset (VerticalJetPatch N),
      (Set.univ ×ˢ Icc (0 : ℝ) 1 : Set (PrimeTorus N × ℝ)) ⊆ ⋃ p ∈ s, p.region ∧
      ∀ p ∈ s, IsOpen p.phases ∧ 0 < p.lower ∧
        ∀ w ∈ p.phases, ∀ u ∈ Icc p.left p.right,
          p.lower ≤ |realVerticalJet a N σ p.order p.component w u| := by
  classical
  choose p hpOpen hpMem hpPos hpBound using exists_vertical_jet_patch hN ha σ
  have hc : IsCompact (Set.univ ×ˢ Icc (0 : ℝ) 1 : Set (PrimeTorus N × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨s, _, hs⟩ := hc.elim_nhds_subcover (fun zt => (p zt).region)
    (fun zt _ => ((hpOpen zt).prod isOpen_Ioo).mem_nhds (hpMem zt))
  refine ⟨s.image p, ?_, ?_⟩
  · intro zt hzt
    obtain ⟨x, hx, h⟩ := Set.mem_iUnion₂.mp (hs hzt)
    exact Set.mem_iUnion₂.mpr ⟨p x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, h⟩
  · intro q hq
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hpOpen x, hpPos x, hpBound x⟩

end

end Dubon2026
