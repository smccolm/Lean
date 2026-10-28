import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place

open AlgebraicCurve
theorem AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F) : ofAlgAut σ • v = σ • v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place.solution
