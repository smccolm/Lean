import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff
