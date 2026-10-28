import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

theorem ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (Ω : Type*) [Field Ω] [Algebra K Ω] (j₀ : Ω) (hj₀ : Transcendental K j₀) :
    ∃ e : {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = j₀} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y},
      ∀ ψ, ((e ψ : {y : Ω //
          (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y}) : Ω) =
        ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental.solution
