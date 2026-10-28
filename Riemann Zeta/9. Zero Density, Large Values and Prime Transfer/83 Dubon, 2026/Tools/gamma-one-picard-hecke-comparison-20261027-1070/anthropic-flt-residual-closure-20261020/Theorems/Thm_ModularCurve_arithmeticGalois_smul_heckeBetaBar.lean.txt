import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticGalois_smul_heckeBetaBar

theorem ModularCurve.arithmeticGalois_smul_heckeBetaBar {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero ℓ] (σ : L ≃ₐ[ℚ] L) (x : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N)) : ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull (N * ℓ)) σ • (ModularCurve.heckeBetaBar L N ℓ x) = ModularCurve.heckeBetaBar L N ℓ (ModularCurve.arithmeticGalois (ModularCurve.modularFunctionFieldFull N) σ • x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticGalois_smul_heckeBetaBar.solution
