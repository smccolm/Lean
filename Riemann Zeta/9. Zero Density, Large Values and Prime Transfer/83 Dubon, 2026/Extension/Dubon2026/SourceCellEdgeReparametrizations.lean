import Dubon2026.SourceCellSameSideTransport

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
namespace Dubon2026.SourceFunctionField.CellGeometry.SegmentReparam
noncomputable section
open scoped Real
open Set

theorem exists_reparam_across_edge :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ), 0 < a → 0 < b →
      R.q.re + a = R'.q.re - b →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹) →
      R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ), 0 < c → 0 < d →
      R.q.im + c = R'.q.im - d →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by
  refine ⟨?_, ?_⟩
  · intro R R' k k' a b ha hb hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.opposite_vertical R R' k k' a b ha hb hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' c d hc hd hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.opposite_horizontal R R' k k' c d hc hd hline hr hw hr' hw' h₁ h₂

theorem exists_reparam_same_side :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ), 0 < a → 0 < a' →
      R.q.re + a = R'.q.re + a' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹) →
      (R'.arcIcc k' ⊆ Ioo (-(π / 2)) (π / 2) ∨ R'.arcIcc k' ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ), 0 < b → 0 < b' →
      R.q.re - b = R'.q.re - b' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹) → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹) → R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ), 0 < c → 0 < c' →
      R.q.im + c = R'.q.im + c' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) → R'.arcIcc k' ⊆ Ioo 0 π →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ), 0 < d → 0 < d' →
      R.q.im - d = R'.q.im - d' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) → R.arcIcc k ⊆ Ioo π (2 * π) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R R' k k' a a' ha ha' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_right R R' k k' a a' ha ha' hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' b b' hb hb' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_left R R' k k' b b' hb hb' hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' c c' hc hc' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_top R R' k k' c c' hc hc' hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' d d' hd hd' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_bottom R R' k k' d d' hd hd' hline hr hw hr' hw' h₁ h₂


end
end Dubon2026.SourceFunctionField.CellGeometry.SegmentReparam
