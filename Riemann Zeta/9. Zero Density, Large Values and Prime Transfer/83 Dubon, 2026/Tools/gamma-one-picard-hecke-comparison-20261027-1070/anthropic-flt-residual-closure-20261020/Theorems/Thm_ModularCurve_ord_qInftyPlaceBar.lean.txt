import Definitions.Def_ModularCurve_QAdicPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_qInftyPlaceBar

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_qInftyPlaceBar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) (f : F) : (qInftyPlaceBar L F h).ord f = (qSeriesBar L F f).order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_qInftyPlaceBar.solution
