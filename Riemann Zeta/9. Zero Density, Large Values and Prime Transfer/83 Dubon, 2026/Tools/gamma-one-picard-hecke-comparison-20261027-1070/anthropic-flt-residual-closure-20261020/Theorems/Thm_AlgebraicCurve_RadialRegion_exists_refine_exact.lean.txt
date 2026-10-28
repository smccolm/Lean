import Definitions.Def_AlgebraicCurve_CellDissection
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_refine_exact

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_refine_exact (R : RadialRegion) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * π) :
    ∃ R' : RadialRegion,
      R'.q = R.q ∧ R'.r = R.r ∧ R'.K = R.K ∧ R'.Kint = R.Kint ∧ R'.loop = R.loop ∧
      Set.range R'.φs = Set.range R.φs ∪ (T : Set ℝ) ∧
      R'.N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard ∧
      (∀ k' : Fin R'.N, ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
        t ∉ Ioo (R'.φs k'.castSucc) (R'.φs k'.succ)) ∧
      (∀ k' : Fin R'.N, ∃ k : Fin R.N, R'.arcIcc k' ⊆ R.arcIcc k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_refine_exact.solution
