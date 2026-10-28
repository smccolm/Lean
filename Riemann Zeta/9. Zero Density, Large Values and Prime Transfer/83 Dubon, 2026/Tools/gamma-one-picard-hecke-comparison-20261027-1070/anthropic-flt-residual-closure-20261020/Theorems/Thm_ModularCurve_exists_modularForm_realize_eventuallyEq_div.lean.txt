import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_realize_eventuallyEq_div
attribute [-simp] ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_modularForm_realize_eventuallyEq_div (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ∧
      ∀ τ : ℍ, (fun z : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_realize_eventuallyEq_div.solution
