import Definitions.Def_AlgebraicCurve_CellDissection
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_rect_sixArcs

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_rect_sixArcs (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    ∃ R : RadialRegion,
      R.q = p ∧ R.N = 6 ∧
      R.K = {z : ℂ | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc y₀ y₁} ∧
      R.Kint = {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁} ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc p.im y₁}) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = y₁ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 2 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc yL y₁}) ∧
      (∀ k : Fin R.N, k.val = 3 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc y₀ yL}) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = y₀ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc y₀ p.im}) ∧
      (∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨x₁, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨x₀, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨x₀, yL⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨x₀, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨x₁, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (x₁ - p.re))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (y₁ - p.im))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (p.re - x₀))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (p.im - y₀))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ R.K, z ∉ R.Kint →
        R.loop (if Complex.arg (z - p) < 0 then Complex.arg (z - p) + 2 * π else Complex.arg (z - p))
          = z) ∧
      (∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
        R.loop '' Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_rect_sixArcs.solution
