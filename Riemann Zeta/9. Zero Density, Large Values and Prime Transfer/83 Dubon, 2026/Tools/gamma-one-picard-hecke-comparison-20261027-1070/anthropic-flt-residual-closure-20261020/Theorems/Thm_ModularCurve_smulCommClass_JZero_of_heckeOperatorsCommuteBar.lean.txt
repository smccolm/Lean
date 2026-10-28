import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar

theorem ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar (N : ℕ) [NeZero N] (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) : letI := ModularCurve.heckeModuleBar N; SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg (ModularCurve.JZero N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.solution
