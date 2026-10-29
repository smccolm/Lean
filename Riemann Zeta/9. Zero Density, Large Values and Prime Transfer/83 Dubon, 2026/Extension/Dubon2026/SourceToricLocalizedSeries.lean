import Dubon2026.SourceToricCoefficientLocalization

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> exact-order toric point -> residue specialization. The already
proved integer coefficient polynomials define the toric abscissa over the
actual algebraic integers with N inverted. Every coefficient specialization
sending the standard primitive root to the prescribed root recovers the
literal divisor-sum series. -/
namespace Dubon2026.SourceFunctionField.ToricAnalytic
noncomputable section
open Polynomial SourceFricke GammaOne.ToricFourier
local notation "Zbar" => integralClosure ℤ ℂ

/-- The toric abscissa over the localized algebraic integers, using the proved integer polynomials. -/
def localizedToricX (N : ℕ) [NeZero N] (c : ZMod N) : PowerSeries (ToricCoefficientRing N) :=
  PowerSeries.mk fun n => levelInverse N ^ 2 *
    (xT N n).eval₂ (Int.castRingHom (ToricCoefficientRing N))
      ((algebraMap Zbar (ToricCoefficientRing N) (integralZeta N)) ^ c.val)

theorem map_localizedToricX (N : ℕ) [NeZero N] (c : ZMod N) (hc : c ≠ 0)
    {K : Type*} [Field K] (f : ToricCoefficientRing N →+* K)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (hf : f (algebraMap Zbar (ToricCoefficientRing N) (integralZeta N)) = ζ) :
    (localizedToricX N c).map f = xS (ζ ^ c.val) := by
  have hN := GammaOne.ToricFourier.natCast_ne_zero hζ
  have hcomp : f.comp (Int.castRingHom (ToricCoefficientRing N)) = Int.castRingHom K :=
    Subsingleton.elim _ _
  ext n
  simp only [PowerSeries.coeff_map, localizedToricX, xS, PowerSeries.coeff_mk,
    map_mul, map_pow, map_levelInverse N f hN, Polynomial.hom_eval₂, hcomp, hf]
  have hx := aeval_xT hζ hc n
  simp only [ψ_apply, aeval_def, algebraMap_int_eq] at hx
  rw [hx]
  field_simp

/-- The literal integral Tate equation over the localized coefficient power series. -/
def localizedTateCurve (N : ℕ) : WeierstrassCurve (PowerSeries (ToricCoefficientRing N)) :=
  tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ToricCoefficientRing N)))

theorem map_localizedTateCurve (N : ℕ) {K : Type*} [CommRing K]
    (f : ToricCoefficientRing N →+* K) :
    (localizedTateCurve N).map (PowerSeries.map f) =
      tatePowerSeries.map (PowerSeries.map (Int.castRingHom K)) := by
  rw [localizedTateCurve, WeierstrassCurve.map_map]
  congr 1
  ext p n
  simp only [RingHom.comp_apply, PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]

end
end Dubon2026.SourceFunctionField.ToricAnalytic
