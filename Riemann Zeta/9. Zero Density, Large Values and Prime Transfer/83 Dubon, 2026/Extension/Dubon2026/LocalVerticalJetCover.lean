import Dubon2026.UnitLogTail

/-! # Vertical derivative patches stable under small changes of the real abscissa -/

namespace Dubon2026

open Filter Set
open scoped Topology

/-- A real-component derivative patch with an open set of abscissae. -/
structure AbscissaJetPatch where
  /-- Derivative order. -/
  order : ℕ
  /-- Real or imaginary component. -/
  component : Bool
  /-- Allowed real abscissae. -/
  abscissae : Set ℝ
  /-- Left height endpoint. -/
  left : ℝ
  /-- Right height endpoint. -/
  right : ℝ
  /-- Lower bound for the selected derivative. -/
  lower : ℝ

theorem continuous_verticalJet_abscissa (a : ℕ → ℂ) (N k : ℕ) (z : PrimeTorus N) :
    Continuous (fun xt : ℝ × ℝ => verticalJet a N xt.1 k z xt.2) := by
  unfold verticalJet
  fun_prop

theorem exists_abscissa_jet_patch {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ t : ℝ) :
    ∃ p : AbscissaJetPatch, IsOpen p.abscissae ∧ σ ∈ p.abscissae ∧
      t ∈ Ioo p.left p.right ∧ 0 < p.lower ∧
        ∀ x ∈ p.abscissae, ∀ y ∈ Icc p.left p.right,
          p.lower ≤ |realVerticalJet a N x p.order p.component 0 y| := by
  obtain ⟨k, hk⟩ := exists_nonzero_verticalJet hN ha σ 0 t
  obtain ⟨b, hb⟩ := exists_realComponent_ne_zero hk
  have hc : Continuous (fun xt : ℝ × ℝ => realVerticalJet a N xt.1 k b 0 xt.2) :=
    (realComponent b).continuous.comp (continuous_verticalJet_abscissa a N k 0)
  obtain ⟨U, l, r, L, hU, hσ, hl, hr, hL, hbound⟩ :=
    exists_rectangle_lower_bound _ hc σ t hb
  exact ⟨⟨k, b, U, l, r, L⟩, hU, hσ, ⟨hl, hr⟩, hL, hbound⟩

theorem exists_finite_local_vertical_jet_cover {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ b t : ℝ) :
    ∃ (s : Finset AbscissaJetPatch) (V : Set ℝ), V ∈ 𝓝 σ ∧
      Icc b t ⊆ ⋃ p ∈ s, Ioo p.left p.right ∧
        ∀ p ∈ s, 0 < p.lower ∧ ∀ x ∈ V, ∀ y ∈ Icc p.left p.right,
          p.lower ≤ |realVerticalJet a N x p.order p.component 0 y| := by
  classical
  choose p hpOpen hpσ hpMem hpPos hpBound using exists_abscissa_jet_patch hN ha σ
  obtain ⟨s, _, hs⟩ := (isCompact_Icc : IsCompact (Icc b t)).elim_nhds_subcover
    (fun y => Ioo (p y).left (p y).right) (fun y _ => isOpen_Ioo.mem_nhds (hpMem y))
  let V := {x : ℝ | ∀ y ∈ s, x ∈ (p y).abscissae}
  have hV : V ∈ 𝓝 σ := by
    exact (eventually_all_finset s).mpr fun y _ => (hpOpen y).mem_nhds (hpσ y)
  refine ⟨s.image p, V, hV, ?_, ?_⟩
  · intro y hy
    obtain ⟨v, hv, h⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact Set.mem_iUnion₂.mpr ⟨p v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, h⟩
  · intro q hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨hpPos y, fun x hx => hpBound y x (hx y hy)⟩

end Dubon2026
