import Definitions.Def_ModularCurve_SpecialisationVocab
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_goodModel_1728_spec

theorem ModularCurve.B3.goodModel_1728_spec :
    IntegralCoeffs (goodModel 1728) ∧ (goodModel 1728).Δ.orderTop = 0 ∧
      ∃ _ : (specialFibre (goodModel 1728)).IsElliptic,
        (specialFibre (goodModel 1728)).j = 1728 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_goodModel_1728_spec.solution
