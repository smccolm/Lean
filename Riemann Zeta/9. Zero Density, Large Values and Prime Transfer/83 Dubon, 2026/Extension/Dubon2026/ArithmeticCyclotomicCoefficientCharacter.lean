import Dubon2026.ArithmeticCyclotomicRestriction

/-! # Actual arithmetic cyclotomic characters in the original coefficient ring -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The canonical scalar value of a finite cyclotomic exponent, using the actual
characteristic map from `ZMod n` to the original coefficient ring. -/
def finiteCyclotomicCoefficientMap (n : ℕ) (k : Type) [CommRing k]
    [CharP k n] [TopologicalSpace k] : (ZMod n)ˣ →ₜ* k where
  toMonoidHom := (ZMod.castHom (dvd_refl n) k).toMonoidHom.comp (Units.coeHom (ZMod n))
  continuous_toFun := continuous_of_discreteTopology

/-- The genuine arithmetic cyclotomic character with values in the original
coefficient ring. Its values are obtained through the canonical characteristic map. -/
def rationalArithmeticCyclotomicCoefficientCharacter
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (k : Type) [CommRing k] [CharP k n] [TopologicalSpace k] :
    rationalArithmeticGaloisGroup a →ₜ* k :=
  (finiteCyclotomicCoefficientMap n k).comp (rationalArithmeticCyclotomicCharacter a n hna)

/-- The genuine cyclotomic character at the actual rational prime completion,
with values in the same original coefficient ring. -/
def rationalPrimeCyclotomicCoefficientCharacter
    (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
    (k : Type) [CommRing k] [CharP k n] [TopologicalSpace k] :
    (rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp) →ₜ* k :=
  (finiteCyclotomicCoefficientMap n k).comp (rationalPrimeCyclotomicCharacter p hp n)

/-- The characteristic map preserves the proved equality of actual global and
local cyclotomic characters along the original arithmetic restriction. The local
prime is arbitrary and need not equal the coefficient characteristic. -/
theorem rationalArithmeticCyclotomicCoefficientCharacter_restriction
    (a : 𝓞 ℚ) (n : ℕ) [NeZero n] (hna : (n : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime)
    (k : Type) [CommRing k] [CharP k n] [TopologicalSpace k] :
    (rationalArithmeticCyclotomicCoefficientCharacter a n hna k).comp
        (rationalPrimeArithmeticRestriction a p hp) =
      rationalPrimeCyclotomicCoefficientCharacter p hp n k := by
  change (finiteCyclotomicCoefficientMap n k).comp
      ((rationalArithmeticCyclotomicCharacter a n hna).comp
        (rationalPrimeArithmeticRestriction a p hp)) = _
  rw [rationalArithmeticCyclotomicCharacter_restriction]
  rfl

end
end Dubon2026
