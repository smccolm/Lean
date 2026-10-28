import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve
theorem ModularCurve.heckeOperatorBar_comm_of_heckeExchangeAt (N ℓ ℓ' M : ℕ) [NeZero N] [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ') (hM' : M = N * ℓ' * ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ'))] [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)] (hex : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) (hex' : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ' ℓ M hM') : heckeOperatorBar N ⟨ℓ, Fact.out⟩ * heckeOperatorBar N ⟨ℓ', Fact.out⟩ = heckeOperatorBar N ⟨ℓ', Fact.out⟩ * heckeOperatorBar N ⟨ℓ, Fact.out⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt.solution
