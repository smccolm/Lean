import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import P2M.Util
import P2M.Sol.S_ModularCurve_StarBank_hassePolyDescent
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open Polynomial HahnSeries ModularCurve UpperHalfPlane
open scoped MatrixGroups
theorem ModularCurve.StarBank.hassePolyDescent {N : ℕ}
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F)
    (h0 : PowerSeries.constantCoeff T ≠ 0) :
    ∃ G : Polynomial ℤ, G.natDegree = N ∧ G.coeff N = PowerSeries.constantCoeff T ∧
      HahnSeries.ofPowerSeries ℤ ℤ T
        = Polynomial.aeval (ModularCurve.jqModC ℤ) G
          * (HahnSeries.single (1 : ℤ) 1
              * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24) ^ N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_hassePolyDescent.solution
