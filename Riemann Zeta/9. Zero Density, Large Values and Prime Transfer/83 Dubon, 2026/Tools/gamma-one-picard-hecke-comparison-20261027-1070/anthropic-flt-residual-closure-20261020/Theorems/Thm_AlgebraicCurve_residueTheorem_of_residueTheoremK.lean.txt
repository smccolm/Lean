import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_residueTheorem_of_residueTheoremK

theorem AlgebraicCurve.residueTheorem_of_residueTheoremK
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (h : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.ResidueTheorem K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_residueTheorem_of_residueTheoremK.solution
