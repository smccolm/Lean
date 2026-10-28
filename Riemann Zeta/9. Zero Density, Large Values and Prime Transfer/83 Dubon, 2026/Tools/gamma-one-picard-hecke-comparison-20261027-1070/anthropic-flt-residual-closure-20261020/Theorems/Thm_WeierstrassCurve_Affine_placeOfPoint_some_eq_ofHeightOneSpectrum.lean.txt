import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.placeOfPoint_some_eq_ofHeightOneSpectrum
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    placeOfPoint (Point.some x y h) = Place.ofHeightOneSpectrum (K := F) w := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum.solution
