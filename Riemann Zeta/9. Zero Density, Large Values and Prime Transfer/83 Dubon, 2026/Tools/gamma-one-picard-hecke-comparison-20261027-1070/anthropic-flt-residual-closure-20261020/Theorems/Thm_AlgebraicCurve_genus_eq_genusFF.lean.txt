import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_genus_eq_genusFF

theorem AlgebraicCurve.genus_eq_genusFF
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_genus_eq_genusFF.solution
