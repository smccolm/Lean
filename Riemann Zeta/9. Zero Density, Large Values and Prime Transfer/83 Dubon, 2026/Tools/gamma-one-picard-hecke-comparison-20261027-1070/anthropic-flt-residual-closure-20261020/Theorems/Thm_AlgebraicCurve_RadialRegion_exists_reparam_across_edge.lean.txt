import Definitions.Def_AlgebraicCurve_CellDissection
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_reparam_across_edge

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_reparam_across_edge :
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
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_reparam_across_edge.solution
