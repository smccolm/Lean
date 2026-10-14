import Dubon2026.RationalPrimeNaturalWittNorm

/-! # The original rational prime completion in the actual cyclotomic field

Retain the literal original coefficient embedding when adjoining the
constructed changed point. These scalar towers are the actual entry maps
for DUB-17's finite auxiliary extension, rather than a renamed local field.
-/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower

/-- The actual Witt fraction field is an algebra over the literal original completion. -/
local instance rationalPrimeWittOriginalAlgebra (p : ℕ) (hp : p.Prime) :
    Algebra (rationalPrimeLocalField p hp) (rationalPrimeWittField p hp) :=
  (rationalPrimeWittFieldMap p hp).toAlgebra

/-- The actual cyclotomic field carries the original completion action through the proved Witt embedding. -/
local instance rationalPrimeWittCyclotomicAlgebra (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Algebra (rationalPrimeLocalField p hp)
      (wittCyclotomicField (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n) :=
  ((algebraMap (rationalPrimeWittField p hp) _).comp (rationalPrimeWittFieldMap p hp)).toAlgebra

/-- This action is the literal composite through the actual Witt fraction field. -/
local instance rationalPrimeWittCyclotomicTower (p : ℕ) (hp : p.Prime) (n : ℕ) :
    IsScalarTower (rationalPrimeLocalField p hp) (rationalPrimeWittField p hp)
      (wittCyclotomicField (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The actual original completion embedding into the cyclotomic field is injective. -/
theorem rationalPrimeWittCyclotomicMap_injective (p : ℕ) (hp : p.Prime) (n : ℕ) :
    Function.Injective (algebraMap (rationalPrimeLocalField p hp)
      (wittCyclotomicField (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)) := by
  exact (algebraMap (rationalPrimeLocalField p hp)
    (wittCyclotomicField (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) n)).injective

end
end Dubon2026
