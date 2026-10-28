import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_tendsto_realize_smul_of_forall_ord_eq_zero
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_tendsto_realize_smul_of_forall_ord_eq_zero (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (hx : x ≠ 0)
    (hord : ∀ v : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
          ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
            (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
          ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∉
        v.toValuationSubring → v.ord x = 0)
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => ModularCurve.realize N (x : LaurentSeries ℂ) (σ • τ))
        atImInfty (𝓝 L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_tendsto_realize_smul_of_forall_ord_eq_zero.solution
