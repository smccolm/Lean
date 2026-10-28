import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound
import P2M.Util
import P2M.Sol.S_HahnSeries_mem_puiseuxRamSubfield_iff

theorem HahnSeries.mem_puiseuxRamSubfield_iff {K : Type*} [Field K] {e : ℕ} (he : 0 < e)
    {y : HahnSeries ℚ K} :
    y ∈ HahnSeries.puiseuxRamSubfield K he ↔ HahnSeries.HasRamBound e y := by p2m_exact_reverting @_root_.P2MW.S_HahnSeries_mem_puiseuxRamSubfield_iff.solution
