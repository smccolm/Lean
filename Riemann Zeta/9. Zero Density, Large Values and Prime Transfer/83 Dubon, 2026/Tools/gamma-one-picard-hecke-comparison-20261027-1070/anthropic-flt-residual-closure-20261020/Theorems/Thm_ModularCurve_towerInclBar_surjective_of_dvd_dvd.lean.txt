import Definitions.Def_ModularCurve_DegeneracyTower
import P2M.Util
import P2M.Sol.S_ModularCurve_towerInclBar_surjective_of_dvd_dvd

open ModularCurve AlgebraicCurve
theorem ModularCurve.towerInclBar_surjective_of_dvd_dvd (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (h' : M ∣ N) : Function.Surjective (towerInclBar L h) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_towerInclBar_surjective_of_dvd_dvd.solution
