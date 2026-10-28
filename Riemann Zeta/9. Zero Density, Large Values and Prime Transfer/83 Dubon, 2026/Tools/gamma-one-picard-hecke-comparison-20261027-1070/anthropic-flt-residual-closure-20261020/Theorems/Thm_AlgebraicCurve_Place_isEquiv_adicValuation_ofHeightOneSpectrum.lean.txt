import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum
