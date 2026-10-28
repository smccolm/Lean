import Definitions.Def_ModularCurve_X0
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ) (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ))) (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) : IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant.solution
