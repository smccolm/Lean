import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_order_qExpand

open ModularCurve

theorem ModularCurve.order_qExpand {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : LaurentSeries R) : (qExpand R N f).order = N * f.order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_order_qExpand.solution
