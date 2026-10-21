import Dubon2026.SourceCurveDivisors
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> regular differential dimension -> canonical divisors.
The source canonical divisor records the actual local differential orders;
its finite support is an obligation proved for the original field downstream.
Selected definition from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_CanonicalDivisor.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Each nonzero differential has a finite divisor of its actual local orders. -/
class HasCanonicalDivisor : Prop where
  /-- The canonical divisor agrees at every actual place with the differential order. -/
  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
    ∀ v : Place K F, D v = v.ordDifferential ω

/-- A canonical divisor with exactly the local orders of the supplied nonzero differential. -/
def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Divisor K F :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose

theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :
    canonicalDivisorOf hω v = v.ordDifferential ω :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose_spec v

end
end Dubon2026.SourceCurve
