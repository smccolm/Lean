import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq {K : Type*} [Field K] [Algebra ℚ K] (hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) → ∃ r : ℚ, algebraMap ℚ K r = c) {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) : f ∈ Set.range (coeffEmb K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq.solution
