import Definitions.Def_ModularCurve_AtkinLehnerPartial
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ σ : modularFunctionFieldFull (N * p) ≃ₐ[ℚ] modularFunctionFieldFull (N * p),
      IsAtkinLehnerAutFull N p σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd.solution
