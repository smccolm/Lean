import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional

open AlgebraicCurve

theorem AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] (w : Place K F') : 0 < w.inertiaDeg F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional.solution
