import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_ModularCurve_rep_tateModule_jZero_comm

theorem ModularCurve.rep_tateModule_jZero_comm (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlg)
    (x : TateModule p (ModularCurve.JZero N)) :
    letI := ModularCurve.heckeModuleBar N
    TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T x)
      = TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T
        (TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_rep_tateModule_jZero_comm.solution
