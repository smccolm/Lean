import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import P2M.Util
namespace P2MW.S_ModularCurve_rep_tateModule_jZero_comm

set_option autoImplicit false

open ModularCurve

theorem solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlg)
    (x : TateModule p (ModularCurve.JZero N)) :
    letI := ModularCurve.heckeModuleBar N
    TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T x)
      = TateModule.rep p (ModularCurve.JZero N) ModularCurve.HeckeAlg T
        (TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by
  letI := ModularCurve.heckeModuleBar N
  haveI := ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar N hcomm
  refine Subtype.ext (funext fun n => ?_)
  simp only [TateModule.rep_apply]
  exact smul_comm σ T ((x : ℕ → JZero N) n)
