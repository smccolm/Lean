import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_CanonicalDivisor
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option synthInstance.maxHeartbeats 200000

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
    (N : ℕ) [NeZero N]
    [∀ w : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      w.DCoordGenerates]
    (a x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (hreg : ∀ v : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
          ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
            (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
          ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∉
        v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => ModularCurve.realize N (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.solution
