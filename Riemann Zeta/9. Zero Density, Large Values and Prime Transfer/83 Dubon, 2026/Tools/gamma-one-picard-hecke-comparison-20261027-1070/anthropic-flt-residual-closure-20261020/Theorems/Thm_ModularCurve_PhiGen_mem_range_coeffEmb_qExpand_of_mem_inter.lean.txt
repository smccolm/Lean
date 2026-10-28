import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {f : LaurentSeries K} (h1 : f ∈ Set.range (ModularCurve.qExpand K ℓ)) (h2 : f ∈ Set.range (coeffEmb K)) : ∃ g : LaurentSeries ℚ, f = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter.solution
