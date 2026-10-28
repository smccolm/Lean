import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_goodModel_generic_spec

open ModularCurve.TatePoint
theorem ModularCurve.B3.goodModel_generic_spec (j₀ : Qbar) (h0 : j₀ ≠ 0) (h1728 : j₀ ≠ 1728) :
    IntegralCoeffs (goodModel j₀) ∧ (goodModel j₀).Δ.orderTop = 0 ∧
      specialFibre (goodModel j₀) = WeierstrassCurve.ofJ j₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_goodModel_generic_spec.solution
