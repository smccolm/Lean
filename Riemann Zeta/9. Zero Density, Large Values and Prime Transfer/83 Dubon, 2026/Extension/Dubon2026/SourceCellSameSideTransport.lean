import Dubon2026.SourceCellOppositeSideTransport

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

theorem same_right (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ)
    (ha : 0 < a) (ha' : 0 < a') (hline : R.q.re + a = R'.q.re + a')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨
      R'.arcIcc k' ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := right_shape R k ha rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := right_shape R' k' ha' hline.symm hr' hw'
  exact core_mono (vert_injective (R.q.re + a)) hl hl' hgh hhg (comp_mono_of_mono_mono hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_left (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ)
    (hb : 0 < b) (hb' : 0 < b') (hline : R.q.re - b = R'.q.re - b')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo (π / 2) (3 * π / 2))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := left_shape R k hb rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := left_shape R' k' hb' hline.symm hr' hw'
  exact core_mono (vert_injective (R.q.re - b)) hl hl' hgh hhg (comp_mono_of_anti_anti hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_top (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ)
    (hc : 0 < c) (hc' : 0 < c') (hline : R.q.im + c = R'.q.im + c')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) (hw : R.arcIcc k ⊆ Set.Ioo 0 π)
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) (hw' : R'.arcIcc k' ⊆ Set.Ioo 0 π)
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := top_shape R k hc rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := top_shape R' k' hc' hline.symm hr' hw'
  exact core_mono (horiz_injective (R.q.im + c)) hl hl' hgh hhg (comp_mono_of_anti_anti hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_bottom (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ)
    (hd : 0 < d) (hd' : 0 < d') (hline : R.q.im - d = R'.q.im - d')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) (hw : R.arcIcc k ⊆ Set.Ioo π (2 * π))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo π (2 * π))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := bottom_shape R k hd rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := bottom_shape R' k' hd' hline.symm hr' hw'
  exact core_mono (horiz_injective (R.q.im - d)) hl hl' hgh hhg (comp_mono_of_mono_mono hg hm')
    (hgC h' _ hC') h₁ h₂


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentTransport
