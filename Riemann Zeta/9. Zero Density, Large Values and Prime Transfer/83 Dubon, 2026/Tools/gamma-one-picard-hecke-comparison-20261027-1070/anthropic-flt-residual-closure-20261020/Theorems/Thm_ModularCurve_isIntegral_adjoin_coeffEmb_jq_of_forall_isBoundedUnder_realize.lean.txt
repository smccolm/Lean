import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane in
open scoped MatrixGroups Topology in

theorem ModularCurve.isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize (N : ℕ)
    [NeZero N] (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (hb : ∀ τ : ℍ, Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖ModularCurve.realize N x z‖)) :
    IsIntegral (Algebra.adjoin ℂ ({ModularCurve.coeffEmb ℂ ModularCurve.jq} : Set (LaurentSeries ℂ)))
      x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize.solution
