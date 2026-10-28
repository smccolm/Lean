import Definitions.Def_AlgebraicCurve_CellDissection
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_recip

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_recip (R : RadialRegion) (hq : R.q = 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_recip.solution
