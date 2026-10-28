import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_coeffEmb

theorem ModularCurve.arithmeticGalois_smul_coeffEmb {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries ℚ} (hx : x ∈ F₀) : ModularCurve.arithmeticGalois F₀ σ • (⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L F₀) = ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_coeffEmb.solution
