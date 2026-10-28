import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.exists_algEquiv_modularFunctionFieldBar_atkinLehner (N₀ p : ℕ) [NeZero N₀]
    [NeZero p] (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) :
    ∃ w : ModularCurve.modularFunctionFieldBar (N₀ * p) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.modularFunctionFieldBar (N₀ * p),
      ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ∀ x : ModularCurve.modularFunctionFieldBar (N₀ * p),
        ((x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq) →
          ((w x : ModularCurve.modularFunctionFieldBar (N₀ * p)) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.qExpand (AlgebraicClosure ℚ) p
                (ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq))) ∧
        ((x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.qExpand (AlgebraicClosure ℚ) p
                (ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq)) →
          ((w x : ModularCurve.modularFunctionFieldBar (N₀ * p)) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner.solution
