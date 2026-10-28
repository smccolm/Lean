import Definitions.Def_ModularCurve_SpecialisationVocab
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_goodModel_zero_spec

theorem ModularCurve.B3.goodModel_zero_spec :
    IntegralCoeffs (goodModel 0) ∧ (goodModel 0).Δ.orderTop = 0 ∧
      ∃ _ : (specialFibre (goodModel 0)).IsElliptic, (specialFibre (goodModel 0)).j = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_goodModel_zero_spec.solution
