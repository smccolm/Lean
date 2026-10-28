import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_prime_not_mem_fullC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.jqNModC_prime_not_mem_fullC {K : Type*} [Field K] (M : ℕ) [NeZero M]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'})
    (hbase : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    jqNModC K p ∉ IntermediateField.adjoin K
      {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_prime_not_mem_fullC.solution
