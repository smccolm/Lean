import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.Thm_AlgebraicCurve_Place_eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits
import P2M.Util
namespace P2MW.S_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum

set_option autoImplicit false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    placeOfPoint (Point.some x y h) = Place.ofHeightOneSpectrum (K := F) w :=
  AlgebraicCurve.Place.eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits
    (placeOfPoint (Point.some x y h))
    (GenusOnePlaceGate.IsCentred.algebraMap_XClass_mem_nonunits h)
    (GenusOnePlaceGate.IsCentred.algebraMap_YClass_mem_nonunits h) w hw
