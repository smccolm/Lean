import Mathlib
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import P2M.Util
namespace P2MW.S_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch

open AlgebraicCurve KaehlerDifferential

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) := by
  have h0 := hRR hω 0
  rw [map_zero, ell_zero_eq_one_of_constantsAreBase hC, sub_zero] at h0
  push_cast at h0
  linarith
