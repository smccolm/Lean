import Dubon2026.SourceCellSegmentTransport

/-! DUB-17/18 -> original Abel-Jacobi -> actual boundary pairing.
Opposite sides require a decreasing C1 reparametrization; square-to-window
sides require an increasing one before reciprocal reversal. Exact endpoint
and loop identities are retained for the lifted original-cell pairing.
The two external reparametrization files contain the same shared proof;
adapt it once, reusing the existing shifted tangent and cotangent lemmas.
Unused affine-transport generalizations are omitted.
Source: anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
noncomputable section
open scoped Real
open Set

theorem opposite_vertical (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hline : R.q.re + a = R'.q.re - b)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo (π / 2) (3 * π / 2))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc)) :
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := right_shape R k ha rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := left_shape R' k' hb hline.symm hr' hw'
  exact core_anti (vert_injective (R.q.re + a)) hl hl' hgh hhg (comp_anti_of_mono_anti hg hm')
    (hgC h' _ hC') h₁ h₂

theorem opposite_horizontal (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hline : R.q.im + c = R'.q.im - d)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) (hw : R.arcIcc k ⊆ Set.Ioo 0 π)
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo π (2 * π))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc)) :
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := top_shape R k hc rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := bottom_shape R' k' hd hline.symm hr' hw'
  exact core_anti (horiz_injective (R.q.im + c)) hl hl' hgh hhg (comp_anti_of_anti_mono hg hm')
    (hgC h' _ hC') h₁ h₂


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
