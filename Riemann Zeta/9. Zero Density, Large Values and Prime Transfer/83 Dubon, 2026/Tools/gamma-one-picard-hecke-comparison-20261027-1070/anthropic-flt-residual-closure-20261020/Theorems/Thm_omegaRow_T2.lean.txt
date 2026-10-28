import Definitions.Def_ModularCurve_OmegaOf
import Definitions.Def_ModularCurve_EigenformIdeal
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_CuspForm_IntegralStructure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import P2M.Util
import P2M.Sol.S_omegaRow_T2
attribute [-simp] ModularCurve.jqNModC_one

open UpperHalfPlane ModularCurve AlgebraicCurve
theorem omegaRow_T2 :
    coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 *
          ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_omegaRow_T2.solution
